import V185TrunkScan22Chunk412

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3683162 : List Nat := [3, 1, 1, 2, 1, 6, 2, 1, 1, 4]
def baseStart_3683162 : Nat := 118140960795 + 3683162 * 2 ^ 59
def prefixEnd_3683162 : Nat := 4983230072969 + 3 ^ 40 * 3683162 * 2
def baseEnd_3683162 : Nat := 1260821622916815896957635

theorem tailTrace_3683162 : CollatzResearch.WordTrace tailWord_3683162 prefixEnd_3683162 1260821622916815896957635 := by
  unfold tailWord_3683162
  simp only [CollatzResearch.WordTrace]
  refine ⟨33583988570635145708688935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89557302855027055223170493 33583988570635145708688935)
  ·
    refine ⟨50375982855952718563033403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33583988570635145708688935 50375982855952718563033403)
    ·
      refine ⟨75563974283929077844550105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50375982855952718563033403 75563974283929077844550105)
      ·
        refine ⟨56672980712946808383412579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75563974283929077844550105 56672980712946808383412579)
        ·
          refine ⟨85009471069420212575118869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56672980712946808383412579 85009471069420212575118869)
          ·
            refine ⟨3984818956379072464458697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 85009471069420212575118869 3984818956379072464458697)
            ·
              refine ⟨2988614217284304348344023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3984818956379072464458697 2988614217284304348344023)
              ·
                refine ⟨4482921325926456522516035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2988614217284304348344023 4482921325926456522516035)
                ·
                  refine ⟨6724381988889684783774053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4482921325926456522516035 6724381988889684783774053)
                  ·
                    refine ⟨1260821622916815896957635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6724381988889684783774053 1260821622916815896957635)
                    ·
                      rfl

theorem cell22_3683162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 1, 4].length) (baseStart_3683162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683162 prefixEnd_3683162 := by exact prefixLift 3683162
  have htrace : WordTrace (prefixWord ++ tailWord_3683162) baseStart_3683162 baseEnd_3683162 := by
    simpa [prefixWord, tailWord_3683162, baseEnd_3683162] using wordTrace_append hprefix tailTrace_3683162
  have hstable : (prefixWord ++ tailWord_3683162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683162).length < 2 ^ (prefixWord ++ tailWord_3683162).sum := by decide
  have hdescent : baseEnd_3683162 < baseStart_3683162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683173 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 2, 4]
def baseStart_3683173 : Nat := 118140960795 + 3683173 * 2 ^ 59
def prefixEnd_3683173 : Nat := 4983230072969 + 3 ^ 40 * 3683173 * 2
def baseEnd_3683173 : Nat := 1260825388441615534932601

theorem tailTrace_3683173 : CollatzResearch.WordTrace tailWord_3683173 prefixEnd_3683173 1260825388441615534932601 := by
  unfold tailWord_3683173
  simp only [CollatzResearch.WordTrace]
  refine ⟨134336355485500731713406173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89557570323667154475604115 134336355485500731713406173)
  ·
    refine ⟨50376133307062774392527315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134336355485500731713406173 50376133307062774392527315)
    ·
      refine ⟨75564199960594161588790973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50376133307062774392527315 75564199960594161588790973)
      ·
        refine ⟨28336574985222810595796615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75564199960594161588790973 28336574985222810595796615)
        ·
          refine ⟨42504862477834215893694923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28336574985222810595796615 42504862477834215893694923)
          ·
            refine ⟨63757293716751323840542385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42504862477834215893694923 63757293716751323840542385)
            ·
              refine ⟨47817970287563492880406789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63757293716751323840542385 47817970287563492880406789)
              ·
                refine ⟨8965869428918154915076273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47817970287563492880406789 8965869428918154915076273)
                ·
                  refine ⟨6724402071688616186307205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8965869428918154915076273 6724402071688616186307205)
                  ·
                    refine ⟨1260825388441615534932601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6724402071688616186307205 1260825388441615534932601)
                    ·
                      rfl

theorem cell22_3683173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_3683173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683173 prefixEnd_3683173 := by exact prefixLift 3683173
  have htrace : WordTrace (prefixWord ++ tailWord_3683173) baseStart_3683173 baseEnd_3683173 := by
    simpa [prefixWord, tailWord_3683173, baseEnd_3683173] using wordTrace_append hprefix tailTrace_3683173
  have hstable : (prefixWord ++ tailWord_3683173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683173).length < 2 ^ (prefixWord ++ tailWord_3683173).sum := by decide
  have hdescent : baseEnd_3683173 < baseStart_3683173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683175 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 4, 3]
def baseStart_3683175 : Nat := 118140960795 + 3683175 * 2 ^ 59
def prefixEnd_3683175 : Nat := 4983230072969 + 3 ^ 40 * 3683175 * 2
def baseEnd_3683175 : Nat := 1260826073082488196382595

theorem tailTrace_3683175 : CollatzResearch.WordTrace tailWord_3683175 prefixEnd_3683175 1260826073082488196382595 := by
  unfold tailWord_3683175
  simp only [CollatzResearch.WordTrace]
  refine ⟨134336428431493486054978979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89557618954328990703319319 134336428431493486054978979)
  ·
    refine ⟨201504642647240229082468469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134336428431493486054978979 201504642647240229082468469)
    ·
      refine ⟨18891060248178771476481419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201504642647240229082468469 18891060248178771476481419)
      ·
        refine ⟨28336590372268157214722129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18891060248178771476481419 28336590372268157214722129)
        ·
          refine ⟨21252442779201117911041597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28336590372268157214722129 21252442779201117911041597)
          ·
            refine ⟨7969666042200419216640599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21252442779201117911041597 7969666042200419216640599)
            ·
              refine ⟨11954499063300628824960899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7969666042200419216640599 11954499063300628824960899)
              ·
                refine ⟨17931748594950943237441349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11954499063300628824960899 17931748594950943237441349)
                ·
                  refine ⟨3362202861553301857020253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17931748594950943237441349 3362202861553301857020253)
                  ·
                    refine ⟨1260826073082488196382595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3362202861553301857020253 1260826073082488196382595)
                    ·
                      rfl

theorem cell22_3683175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_3683175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683175 prefixEnd_3683175 := by exact prefixLift 3683175
  have htrace : WordTrace (prefixWord ++ tailWord_3683175) baseStart_3683175 baseEnd_3683175 := by
    simpa [prefixWord, tailWord_3683175, baseEnd_3683175] using wordTrace_append hprefix tailTrace_3683175
  have hstable : (prefixWord ++ tailWord_3683175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683175).length < 2 ^ (prefixWord ++ tailWord_3683175).sum := by decide
  have hdescent : baseEnd_3683175 < baseStart_3683175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683190 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_3683190 : Nat := 118140960795 + 3683190 * 2 ^ 59
def prefixEnd_3683190 : Nat := 4983230072969 + 3 ^ 40 * 3683190 * 2
def baseEnd_3683190 : Nat := 1260831207889033157257549

theorem tailTrace_3683190 : CollatzResearch.WordTrace tailWord_3683190 prefixEnd_3683190 1260831207889033157257549 := by
  unfold tailWord_3683190
  simp only [CollatzResearch.WordTrace]
  refine ⟨8396060970402446476048439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89557983684292762411183349 8396060970402446476048439)
  ·
    refine ⟨12594091455603669714072659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8396060970402446476048439 12594091455603669714072659)
    ·
      refine ⟨18891137183405504571108989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12594091455603669714072659 18891137183405504571108989)
      ·
        refine ⟨7084176443777064214165871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18891137183405504571108989 7084176443777064214165871)
        ·
          refine ⟨10626264665665596321248807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7084176443777064214165871 10626264665665596321248807)
          ·
            refine ⟨15939396998498394481873211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10626264665665596321248807 15939396998498394481873211)
            ·
              refine ⟨23909095497747591722809817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15939396998498394481873211 23909095497747591722809817)
              ·
                refine ⟨17931821623310693792107363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23909095497747591722809817 17931821623310693792107363)
                ·
                  refine ⟨26897732434966040688161045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17931821623310693792107363 26897732434966040688161045)
                  ·
                    refine ⟨1260831207889033157257549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26897732434966040688161045 1260831207889033157257549)
                    ·
                      rfl

theorem cell22_3683190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_3683190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683190 prefixEnd_3683190 := by exact prefixLift 3683190
  have htrace : WordTrace (prefixWord ++ tailWord_3683190) baseStart_3683190 baseEnd_3683190 := by
    simpa [prefixWord, tailWord_3683190, baseEnd_3683190] using wordTrace_append hprefix tailTrace_3683190
  have hstable : (prefixWord ++ tailWord_3683190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683190).length < 2 ^ (prefixWord ++ tailWord_3683190).sum := by decide
  have hdescent : baseEnd_3683190 < baseStart_3683190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683205 : List Nat := [1, 3, 1, 1, 3, 5, 2, 6]
def baseStart_3683205 : Nat := 118140960795 + 3683205 * 2 ^ 59
def prefixEnd_3683205 : Nat := 4983230072969 + 3 ^ 40 * 3683205 * 2
def baseEnd_3683205 : Nat := 140092926966175346459167

theorem tailTrace_3683205 : CollatzResearch.WordTrace tailWord_3683205 prefixEnd_3683205 140092926966175346459167 := by
  unfold tailWord_3683205
  simp only [CollatzResearch.WordTrace]
  refine ⟨134337522621384801178571069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89558348414256534119047379 134337522621384801178571069)
  ·
    refine ⟨50376570983019300441964151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134337522621384801178571069 50376570983019300441964151)
    ·
      refine ⟨75564856474528950662946227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50376570983019300441964151 75564856474528950662946227)
      ·
        refine ⟨113347284711793425994419341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75564856474528950662946227 113347284711793425994419341)
        ·
          refine ⟨42505231766922534747907253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113347284711793425994419341 42505231766922534747907253)
          ·
            refine ⟨3984865478148987632616305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42505231766922534747907253 3984865478148987632616305)
            ·
              refine ⟨2988649108611740724462229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3984865478148987632616305 2988649108611740724462229)
              ·
                refine ⟨140092926966175346459167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2988649108611740724462229 140092926966175346459167)
                ·
                  rfl

theorem cell22_3683205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 6].length) (baseStart_3683205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683205 prefixEnd_3683205 := by exact prefixLift 3683205
  have htrace : WordTrace (prefixWord ++ tailWord_3683205) baseStart_3683205 baseEnd_3683205 := by
    simpa [prefixWord, tailWord_3683205, baseEnd_3683205] using wordTrace_append hprefix tailTrace_3683205
  have hstable : (prefixWord ++ tailWord_3683205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683205).length < 2 ^ (prefixWord ++ tailWord_3683205).sum := by decide
  have hdescent : baseEnd_3683205 < baseStart_3683205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683222 : List Nat := [5, 3, 1, 1, 1, 1, 10]
def baseStart_3683222 : Nat := 118140960795 + 3683222 * 2 ^ 59
def prefixEnd_3683222 : Nat := 4983230072969 + 3 ^ 40 * 3683222 * 2
def baseEnd_3683222 : Nat := 46697857857147990387313

theorem tailTrace_3683222 : CollatzResearch.WordTrace tailWord_3683222 prefixEnd_3683222 46697857857147990387313 := by
  unfold tailWord_3683222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8396133916395200817621245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89558761774882142054626613 8396133916395200817621245)
  ·
    refine ⟨3148550218648200306607967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8396133916395200817621245 3148550218648200306607967)
    ·
      refine ⟨4722825327972300459911951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3148550218648200306607967 4722825327972300459911951)
      ·
        refine ⟨7084237991958450689867927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4722825327972300459911951 7084237991958450689867927)
        ·
          refine ⟨10626356987937676034801891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7084237991958450689867927 10626356987937676034801891)
          ·
            refine ⟨15939535481906514052202837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10626356987937676034801891 15939535481906514052202837)
            ·
              refine ⟨46697857857147990387313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15939535481906514052202837 46697857857147990387313)
              ·
                rfl

theorem cell22_3683222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 10].length) (baseStart_3683222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683222 prefixEnd_3683222 := by exact prefixLift 3683222
  have htrace : WordTrace (prefixWord ++ tailWord_3683222) baseStart_3683222 baseEnd_3683222 := by
    simpa [prefixWord, tailWord_3683222, baseEnd_3683222] using wordTrace_append hprefix tailTrace_3683222
  have hstable : (prefixWord ++ tailWord_3683222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683222).length < 2 ^ (prefixWord ++ tailWord_3683222).sum := by decide
  have hdescent : baseEnd_3683222 < baseStart_3683222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683346 : List Nat := [3, 2, 5, 1, 1, 1, 2, 1, 6]
def baseStart_3683346 : Nat := 118140960795 + 3683346 * 2 ^ 59
def prefixEnd_3683346 : Nat := 4983230072969 + 3 ^ 40 * 3683346 * 2
def baseEnd_3683346 : Nat := 420294869959033583452357

theorem tailTrace_3683346 : CollatzResearch.WordTrace tailWord_3683346 prefixEnd_3683346 420294869959033583452357 := by
  unfold tailWord_3683346
  simp only [CollatzResearch.WordTrace]
  refine ⟨33585666328468495564863473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89561776875915988172969261 33585666328468495564863473)
  ·
    refine ⟨25189249746351371673647605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33585666328468495564863473 25189249746351371673647605)
    ·
      refine ⟨2361492163720441094404463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25189249746351371673647605 2361492163720441094404463)
      ·
        refine ⟨3542238245580661641606695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2361492163720441094404463 3542238245580661641606695)
        ·
          refine ⟨5313357368370992462410043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3542238245580661641606695 5313357368370992462410043)
          ·
            refine ⟨7970036052556488693615065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5313357368370992462410043 7970036052556488693615065)
            ·
              refine ⟨5977527039417366520211299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7970036052556488693615065 5977527039417366520211299)
              ·
                refine ⟨8966290559126049780316949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5977527039417366520211299 8966290559126049780316949)
                ·
                  refine ⟨420294869959033583452357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8966290559126049780316949 420294869959033583452357)
                  ·
                    rfl

theorem cell22_3683346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_3683346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683346 prefixEnd_3683346 := by exact prefixLift 3683346
  have htrace : WordTrace (prefixWord ++ tailWord_3683346) baseStart_3683346 baseEnd_3683346 := by
    simpa [prefixWord, tailWord_3683346, baseEnd_3683346] using wordTrace_append hprefix tailTrace_3683346
  have hstable : (prefixWord ++ tailWord_3683346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683346).length < 2 ^ (prefixWord ++ tailWord_3683346).sum := by decide
  have hdescent : baseEnd_3683346 < baseStart_3683346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683353 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 1, 8]
def baseStart_3683353 : Nat := 118140960795 + 3683353 * 2 ^ 59
def prefixEnd_3683353 : Nat := 4983230072969 + 3 ^ 40 * 3683353 * 2
def baseEnd_3683353 : Nat := 1260887006120155065432049

theorem tailTrace_3683353 : CollatzResearch.WordTrace tailWord_3683353 prefixEnd_3683353 1260887006120155065432049 := by
  unfold tailWord_3683353
  simp only [CollatzResearch.WordTrace]
  refine ⟨134342920624848622454958713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89561947083232414969972475 134342920624848622454958713)
  ·
    refine ⟨100757190468636466841219035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134342920624848622454958713 100757190468636466841219035)
    ·
      refine ⟨151135785702954700261828553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100757190468636466841219035 151135785702954700261828553)
      ·
        refine ⟨113351839277216025196371415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151135785702954700261828553 113351839277216025196371415)
        ·
          refine ⟨170027758915824037794557123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113351839277216025196371415 170027758915824037794557123)
          ·
            refine ⟨255041638373736056691835685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170027758915824037794557123 255041638373736056691835685)
            ·
              refine ⟨47820307195075510629719191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255041638373736056691835685 47820307195075510629719191)
              ·
                refine ⟨71730460792613265944578787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47820307195075510629719191 71730460792613265944578787)
                ·
                  refine ⟨107595691188919898916868181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71730460792613265944578787 107595691188919898916868181)
                  ·
                    refine ⟨1260887006120155065432049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107595691188919898916868181 1260887006120155065432049)
                    ·
                      rfl

theorem cell22_3683353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 8].length) (baseStart_3683353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683353 prefixEnd_3683353 := by exact prefixLift 3683353
  have htrace : WordTrace (prefixWord ++ tailWord_3683353) baseStart_3683353 baseEnd_3683353 := by
    simpa [prefixWord, tailWord_3683353, baseEnd_3683353] using wordTrace_append hprefix tailTrace_3683353
  have hstable : (prefixWord ++ tailWord_3683353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683353).length < 2 ^ (prefixWord ++ tailWord_3683353).sum := by decide
  have hdescent : baseEnd_3683353 < baseStart_3683353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683385 : List Nat := [1, 2, 1, 5, 2, 1, 1, 2, 7]
def baseStart_3683385 : Nat := 118140960795 + 3683385 * 2 ^ 59
def prefixEnd_3683385 : Nat := 4983230072969 + 3 ^ 40 * 3683385 * 2
def baseEnd_3683385 : Nat := 420299320124705882877317

theorem tailTrace_3683385 : CollatzResearch.WordTrace tailWord_3683385 prefixEnd_3683385 420299320124705882877317 := by
  unfold tailWord_3683385
  simp only [CollatzResearch.WordTrace]
  refine ⟨134344087760732691920123609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89562725173821794613415739 134344087760732691920123609)
  ·
    refine ⟨100758065820549518940092707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134344087760732691920123609 100758065820549518940092707)
    ·
      refine ⟨151137098730824278410139061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100758065820549518940092707 151137098730824278410139061)
      ·
        refine ⟨14169103006014776100950537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151137098730824278410139061 14169103006014776100950537)
        ·
          refine ⟨10626827254511082075712903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14169103006014776100950537 10626827254511082075712903)
          ·
            refine ⟨15940240881766623113569355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10626827254511082075712903 15940240881766623113569355)
            ·
              refine ⟨23910361322649934670354033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15940240881766623113569355 23910361322649934670354033)
              ·
                refine ⟨17932770991987451002765525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23910361322649934670354033 17932770991987451002765525)
                ·
                  refine ⟨420299320124705882877317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17932770991987451002765525 420299320124705882877317)
                  ·
                    rfl

theorem cell22_3683385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 2, 7].length) (baseStart_3683385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683385 prefixEnd_3683385 := by exact prefixLift 3683385
  have htrace : WordTrace (prefixWord ++ tailWord_3683385) baseStart_3683385 baseEnd_3683385 := by
    simpa [prefixWord, tailWord_3683385, baseEnd_3683385] using wordTrace_append hprefix tailTrace_3683385
  have hstable : (prefixWord ++ tailWord_3683385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683385).length < 2 ^ (prefixWord ++ tailWord_3683385).sum := by decide
  have hdescent : baseEnd_3683385 < baseStart_3683385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683406 : List Nat := [4, 1, 1, 1, 1, 3, 5, 2, 1, 3]
def baseStart_3683406 : Nat := 118140960795 + 3683406 * 2 ^ 59
def prefixEnd_3683406 : Nat := 4983230072969 + 3 ^ 40 * 3683406 * 2
def baseEnd_3683406 : Nat := 1260905149103280593856887

theorem tailTrace_3683406 : CollatzResearch.WordTrace tailWord_3683406 prefixEnd_3683406 1260905149103280593856887 := by
  unfold tailWord_3683406
  simp only [CollatzResearch.WordTrace]
  refine ⟨16793106711707076563329759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89563235795771075004425381 16793106711707076563329759)
  ·
    refine ⟨25189660067560614844994639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16793106711707076563329759 25189660067560614844994639)
    ·
      refine ⟨37784490101340922267491959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25189660067560614844994639 37784490101340922267491959)
      ·
        refine ⟨56676735152011383401237939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37784490101340922267491959 56676735152011383401237939)
        ·
          refine ⟨85015102728017075101856909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56676735152011383401237939 85015102728017075101856909)
          ·
            refine ⟨31880663523006403163196341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85015102728017075101856909 31880663523006403163196341)
            ·
              refine ⟨2988812205281850296549657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31880663523006403163196341 2988812205281850296549657)
              ·
                refine ⟨2241609153961387722412243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2988812205281850296549657 2241609153961387722412243)
                ·
                  refine ⟨3362413730942081583618365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2241609153961387722412243 3362413730942081583618365)
                  ·
                    refine ⟨1260905149103280593856887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3362413730942081583618365 1260905149103280593856887)
                    ·
                      rfl

theorem cell22_3683406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_3683406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683406 prefixEnd_3683406 := by exact prefixLift 3683406
  have htrace : WordTrace (prefixWord ++ tailWord_3683406) baseStart_3683406 baseEnd_3683406 := by
    simpa [prefixWord, tailWord_3683406, baseEnd_3683406] using wordTrace_append hprefix tailTrace_3683406
  have hstable : (prefixWord ++ tailWord_3683406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683406).length < 2 ^ (prefixWord ++ tailWord_3683406).sum := by decide
  have hdescent : baseEnd_3683406 < baseStart_3683406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683415 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 3, 4]
def baseStart_3683415 : Nat := 118140960795 + 3683415 * 2 ^ 59
def prefixEnd_3683415 : Nat := 4983230072969 + 3 ^ 40 * 3683415 * 2
def baseEnd_3683415 : Nat := 1260908229987207570381859

theorem tailTrace_3683415 : CollatzResearch.WordTrace tailWord_3683415 prefixEnd_3683415 1260908229987207570381859 := by
  unfold tailWord_3683415
  simp only [CollatzResearch.WordTrace]
  refine ⟨134345181950624007043715699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89563454633749338029143799 134345181950624007043715699)
  ·
    refine ⟨201517772925936010565573549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134345181950624007043715699 201517772925936010565573549)
    ·
      refine ⟨75569164847226003962090081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201517772925936010565573549 75569164847226003962090081)
      ·
        refine ⟨56676873635419502971567561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75569164847226003962090081 56676873635419502971567561)
        ·
          refine ⟨42507655226564627228675671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56676873635419502971567561 42507655226564627228675671)
          ·
            refine ⟨63761482839846940843013507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42507655226564627228675671 63761482839846940843013507)
            ·
              refine ⟨95642224259770411264520261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63761482839846940843013507 95642224259770411264520261)
              ·
                refine ⟨17932917048706952112097549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95642224259770411264520261 17932917048706952112097549)
                ·
                  refine ⟨6724843893265107042036581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17932917048706952112097549 6724843893265107042036581)
                  ·
                    refine ⟨1260908229987207570381859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6724843893265107042036581 1260908229987207570381859)
                    ·
                      rfl

theorem cell22_3683415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_3683415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683415 prefixEnd_3683415 := by exact prefixLift 3683415
  have htrace : WordTrace (prefixWord ++ tailWord_3683415) baseStart_3683415 baseEnd_3683415 := by
    simpa [prefixWord, tailWord_3683415, baseEnd_3683415] using wordTrace_append hprefix tailTrace_3683415
  have hstable : (prefixWord ++ tailWord_3683415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683415).length < 2 ^ (prefixWord ++ tailWord_3683415).sum := by decide
  have hdescent : baseEnd_3683415 < baseStart_3683415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683447 : List Nat := [1, 1, 3, 1, 1, 4, 2, 5, 4]
def baseStart_3683447 : Nat := 118140960795 + 3683447 * 2 ^ 59
def prefixEnd_3683447 : Nat := 4983230072969 + 3 ^ 40 * 3683447 * 2
def baseEnd_3683447 : Nat := 420306394747056717860587

theorem tailTrace_3683447 : CollatzResearch.WordTrace tailWord_3683447 prefixEnd_3683447 420306394747056717860587 := by
  unfold tailWord_3683447
  simp only [CollatzResearch.WordTrace]
  refine ⟨134346349086508076508880595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89564232724338717672587063 134346349086508076508880595)
  ·
    refine ⟨201519523629762114763320893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134346349086508076508880595 201519523629762114763320893)
    ·
      refine ⟨75569821361160793036245335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201519523629762114763320893 75569821361160793036245335)
      ·
        refine ⟨113354732041741189554368003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75569821361160793036245335 113354732041741189554368003)
        ·
          refine ⟨170032098062611784331552005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113354732041741189554368003 170032098062611784331552005)
          ·
            refine ⟨31881018386739709562166001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170032098062611784331552005 31881018386739709562166001)
            ·
              refine ⟨23910763790054782171624501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31881018386739709562166001 23910763790054782171624501)
              ·
                refine ⟨2241634105317635828589797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23910763790054782171624501 2241634105317635828589797)
                ·
                  refine ⟨420306394747056717860587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2241634105317635828589797 420306394747056717860587)
                  ·
                    rfl

theorem cell22_3683447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 4].length) (baseStart_3683447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683447 prefixEnd_3683447 := by exact prefixLift 3683447
  have htrace : WordTrace (prefixWord ++ tailWord_3683447) baseStart_3683447 baseEnd_3683447 := by
    simpa [prefixWord, tailWord_3683447, baseEnd_3683447] using wordTrace_append hprefix tailTrace_3683447
  have hstable : (prefixWord ++ tailWord_3683447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683447).length < 2 ^ (prefixWord ++ tailWord_3683447).sum := by decide
  have hdescent : baseEnd_3683447 < baseStart_3683447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683475 : List Nat := [1, 1, 1, 2, 1, 2, 7, 7]
def baseStart_3683475 : Nat := 118140960795 + 3683475 * 2 ^ 59
def prefixEnd_3683475 : Nat := 4983230072969 + 3 ^ 40 * 3683475 * 2
def baseEnd_3683475 : Nat := 140103196579265268209075

theorem tailTrace_3683475 : CollatzResearch.WordTrace tailWord_3683475 prefixEnd_3683475 140103196579265268209075 := by
  unfold tailWord_3683475
  simp only [CollatzResearch.WordTrace]
  refine ⟨134347370330406637290899879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89564913553604424860599919 134347370330406637290899879)
  ·
    refine ⟨201521055495609955936349819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134347370330406637290899879 201521055495609955936349819)
    ·
      refine ⟨302281583243414933904524729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201521055495609955936349819 302281583243414933904524729)
      ·
        refine ⟨226711187432561200428393547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302281583243414933904524729 226711187432561200428393547)
        ·
          refine ⟨340066781148841800642590321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226711187432561200428393547 340066781148841800642590321)
          ·
            refine ⟨255050085861631350481942741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340066781148841800642590321 255050085861631350481942741)
            ·
              refine ⟨5977736387381984776920533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 255050085861631350481942741 5977736387381984776920533)
              ·
                refine ⟨140103196579265268209075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5977736387381984776920533 140103196579265268209075)
                ·
                  rfl

theorem cell22_3683475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 7].length) (baseStart_3683475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683475 prefixEnd_3683475 := by exact prefixLift 3683475
  have htrace : WordTrace (prefixWord ++ tailWord_3683475) baseStart_3683475 baseEnd_3683475 := by
    simpa [prefixWord, tailWord_3683475, baseEnd_3683475] using wordTrace_append hprefix tailTrace_3683475
  have hstable : (prefixWord ++ tailWord_3683475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683475).length < 2 ^ (prefixWord ++ tailWord_3683475).sum := by decide
  have hdescent : baseEnd_3683475 < baseStart_3683475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683479 : List Nat := [1, 1, 3, 3, 3, 1, 2, 3, 2, 3]
def baseStart_3683479 : Nat := 118140960795 + 3683479 * 2 ^ 59
def prefixEnd_3683479 : Nat := 4983230072969 + 3 ^ 40 * 3683479 * 2
def baseEnd_3683479 : Nat := 1260930138495132736781663

theorem tailTrace_3683479 : CollatzResearch.WordTrace tailWord_3683479 prefixEnd_3683479 1260930138495132736781663 := by
  unfold tailWord_3683479
  simp only [CollatzResearch.WordTrace]
  refine ⟨134347516222392145974045491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89565010814928097316030327 134347516222392145974045491)
  ·
    refine ⟨201521274333588218961068237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134347516222392145974045491 201521274333588218961068237)
    ·
      refine ⟨75570477875095582110400589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201521274333588218961068237 75570477875095582110400589)
      ·
        refine ⟨28338929203160843291400221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75570477875095582110400589 28338929203160843291400221)
        ·
          refine ⟨10627098451185316234275083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28338929203160843291400221 10627098451185316234275083)
          ·
            refine ⟨15940647676777974351412625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10627098451185316234275083 15940647676777974351412625)
            ·
              refine ⟨11955485757583480763559469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15940647676777974351412625 11955485757583480763559469)
              ·
                refine ⟨4483307159093805286334801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11955485757583480763559469 4483307159093805286334801)
                ·
                  refine ⟨3362480369320353964751101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4483307159093805286334801 3362480369320353964751101)
                  ·
                    refine ⟨1260930138495132736781663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3362480369320353964751101 1260930138495132736781663)
                    ·
                      rfl

theorem cell22_3683479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_3683479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683479 prefixEnd_3683479 := by exact prefixLift 3683479
  have htrace : WordTrace (prefixWord ++ tailWord_3683479) baseStart_3683479 baseEnd_3683479 := by
    simpa [prefixWord, tailWord_3683479, baseEnd_3683479] using wordTrace_append hprefix tailTrace_3683479
  have hstable : (prefixWord ++ tailWord_3683479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683479).length < 2 ^ (prefixWord ++ tailWord_3683479).sum := by decide
  have hdescent : baseEnd_3683479 < baseStart_3683479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683535 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 1, 7]
def baseStart_3683535 : Nat := 118140960795 + 3683535 * 2 ^ 59
def prefixEnd_3683535 : Nat := 4983230072969 + 3 ^ 40 * 3683535 * 2
def baseEnd_3683535 : Nat := 1260949308439567257381491

theorem tailTrace_3683535 : CollatzResearch.WordTrace tailWord_3683535 prefixEnd_3683535 1260949308439567257381491 := by
  unfold tailWord_3683535
  simp only [CollatzResearch.WordTrace]
  refine ⟨134349558710189267538084059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89566372473459511692056039 134349558710189267538084059)
  ·
    refine ⟨201524338065283901307126089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134349558710189267538084059 201524338065283901307126089)
    ·
      refine ⟨151143253548962925980344567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201524338065283901307126089 151143253548962925980344567)
      ·
        refine ⟨226714880323444388970516851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151143253548962925980344567 226714880323444388970516851)
        ·
          refine ⟨340072320485166583455775277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226714880323444388970516851 340072320485166583455775277)
          ·
            refine ⟨127527120181937468795915729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340072320485166583455775277 127527120181937468795915729)
            ·
              refine ⟨95645340136453101596936797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127527120181937468795915729 95645340136453101596936797)
              ·
                refine ⟨35867002551169913098851299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95645340136453101596936797 35867002551169913098851299)
                ·
                  refine ⟨53800503826754869648276949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35867002551169913098851299 53800503826754869648276949)
                  ·
                    refine ⟨1260949308439567257381491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53800503826754869648276949 1260949308439567257381491)
                    ·
                      rfl

theorem cell22_3683535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_3683535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683535 prefixEnd_3683535 := by exact prefixLift 3683535
  have htrace : WordTrace (prefixWord ++ tailWord_3683535) baseStart_3683535 baseEnd_3683535 := by
    simpa [prefixWord, tailWord_3683535, baseEnd_3683535] using wordTrace_append hprefix tailTrace_3683535
  have hstable : (prefixWord ++ tailWord_3683535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683535).length < 2 ^ (prefixWord ++ tailWord_3683535).sum := by decide
  have hdescent : baseEnd_3683535 < baseStart_3683535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683612 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 1, 6]
def baseStart_3683612 : Nat := 118140960795 + 3683612 * 2 ^ 59
def prefixEnd_3683612 : Nat := 4983230072969 + 3 ^ 40 * 3683612 * 2
def baseEnd_3683612 : Nat := 1260975667113164723206255

theorem tailTrace_3683612 : CollatzResearch.WordTrace tailWord_3683612 prefixEnd_3683612 1260975667113164723206255 := by
  unfold tailWord_3683612
  simp only [CollatzResearch.WordTrace]
  refine ⟨67176183565455154844318545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89568244753940206459091393 67176183565455154844318545)
  ·
    refine ⟨50382137674091366133238909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67176183565455154844318545 50382137674091366133238909)
    ·
      refine ⟨18893301627784262299964591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50382137674091366133238909 18893301627784262299964591)
      ·
        refine ⟨28339952441676393449946887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18893301627784262299964591 28339952441676393449946887)
        ·
          refine ⟨42509928662514590174920331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28339952441676393449946887 42509928662514590174920331)
          ·
            refine ⟨63764892993771885262380497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42509928662514590174920331 63764892993771885262380497)
            ·
              refine ⟨47823669745328913946785373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63764892993771885262380497 47823669745328913946785373)
              ·
                refine ⟨17933876154498342730044515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47823669745328913946785373 17933876154498342730044515)
                ·
                  refine ⟨26900814231747514095066773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17933876154498342730044515 26900814231747514095066773)
                  ·
                    refine ⟨1260975667113164723206255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26900814231747514095066773 1260975667113164723206255)
                    ·
                      rfl

theorem cell22_3683612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_3683612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683612 prefixEnd_3683612 := by exact prefixLift 3683612
  have htrace : WordTrace (prefixWord ++ tailWord_3683612) baseStart_3683612 baseEnd_3683612 := by
    simpa [prefixWord, tailWord_3683612, baseEnd_3683612] using wordTrace_append hprefix tailTrace_3683612
  have hstable : (prefixWord ++ tailWord_3683612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683612).length < 2 ^ (prefixWord ++ tailWord_3683612).sum := by decide
  have hdescent : baseEnd_3683612 < baseStart_3683612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683618 : List Nat := [3, 3, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_3683618 : Nat := 118140960795 + 3683618 * 2 ^ 59
def prefixEnd_3683618 : Nat := 4983230072969 + 3 ^ 40 * 3683618 * 2
def baseEnd_3683618 : Nat := 1260977721035782707556237

theorem tailTrace_3683618 : CollatzResearch.WordTrace tailWord_3683618 prefixEnd_3683618 1260977721035782707556237 := by
  unfold tailWord_3683618
  simp only [CollatzResearch.WordTrace]
  refine ⟨33588146492222143178338877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89568390645925715142237005 33588146492222143178338877)
  ·
    refine ⟨12595554934583303691877079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33588146492222143178338877 12595554934583303691877079)
    ·
      refine ⟨18893332401874955537815619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12595554934583303691877079 18893332401874955537815619)
      ·
        refine ⟨28339998602812433306723429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18893332401874955537815619 28339998602812433306723429)
        ·
          refine ⟨5313749738027331245010643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28339998602812433306723429 5313749738027331245010643)
          ·
            refine ⟨7970624607040996867515965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5313749738027331245010643 7970624607040996867515965)
            ·
              refine ⟨2988984227640373825318487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7970624607040996867515965 2988984227640373825318487)
              ·
                refine ⟨4483476341460560737977731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2988984227640373825318487 4483476341460560737977731)
                ·
                  refine ⟨6725214512190841106966597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4483476341460560737977731 6725214512190841106966597)
                  ·
                    refine ⟨1260977721035782707556237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6725214512190841106966597 1260977721035782707556237)
                    ·
                      rfl

theorem cell22_3683618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_3683618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683618 prefixEnd_3683618 := by exact prefixLift 3683618
  have htrace : WordTrace (prefixWord ++ tailWord_3683618) baseStart_3683618 baseEnd_3683618 := by
    simpa [prefixWord, tailWord_3683618, baseEnd_3683618] using wordTrace_append hprefix tailTrace_3683618
  have hstable : (prefixWord ++ tailWord_3683618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683618).length < 2 ^ (prefixWord ++ tailWord_3683618).sum := by decide
  have hdescent : baseEnd_3683618 < baseStart_3683618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683633 : List Nat := [1, 2, 2, 3, 3, 3, 2, 2, 4]
def baseStart_3683633 : Nat := 118140960795 + 3683633 * 2 ^ 59
def prefixEnd_3683633 : Nat := 4983230072969 + 3 ^ 40 * 3683633 * 2
def baseEnd_3683633 : Nat := 420327618614109222810397

theorem tailTrace_3683633 : CollatzResearch.WordTrace tailWord_3683633 prefixEnd_3683633 420327618614109222810397 := by
  unfold tailWord_3683633
  simp only [CollatzResearch.WordTrace]
  refine ⟨134353133063834230275151553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89568755375889486850101035 134353133063834230275151553)
  ·
    refine ⟨100764849797875672706363665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134353133063834230275151553 100764849797875672706363665)
    ·
      refine ⟨75573637348406754529772749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100764849797875672706363665 75573637348406754529772749)
      ·
        refine ⟨28340114005652532948664781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75573637348406754529772749 28340114005652532948664781)
        ·
          refine ⟨10627542752119699855749293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28340114005652532948664781 10627542752119699855749293)
          ·
            refine ⟨3985328532044887445905985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10627542752119699855749293 3985328532044887445905985)
            ·
              refine ⟨2988996399033665584429489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3985328532044887445905985 2988996399033665584429489)
              ·
                refine ⟨2241747299275249188322117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2988996399033665584429489 2241747299275249188322117)
                ·
                  refine ⟨420327618614109222810397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2241747299275249188322117 420327618614109222810397)
                  ·
                    rfl

theorem cell22_3683633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 2, 4].length) (baseStart_3683633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683633 prefixEnd_3683633 := by exact prefixLift 3683633
  have htrace : WordTrace (prefixWord ++ tailWord_3683633) baseStart_3683633 baseEnd_3683633 := by
    simpa [prefixWord, tailWord_3683633, baseEnd_3683633] using wordTrace_append hprefix tailTrace_3683633
  have hstable : (prefixWord ++ tailWord_3683633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683633).length < 2 ^ (prefixWord ++ tailWord_3683633).sum := by decide
  have hdescent : baseEnd_3683633 < baseStart_3683633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683644 : List Nat := [2, 2, 2, 2, 1, 5, 1, 7]
def baseStart_3683644 : Nat := 118140960795 + 3683644 * 2 ^ 59
def prefixEnd_3683644 : Nat := 4983230072969 + 3 ^ 40 * 3683644 * 2
def baseEnd_3683644 : Nat := 140109624596347478489573

theorem tailTrace_3683644 : CollatzResearch.WordTrace tailWord_3683644 prefixEnd_3683644 140109624596347478489573 := by
  unfold tailWord_3683644
  simp only [CollatzResearch.WordTrace]
  refine ⟨67176767133397189576900993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89569022844529586102534657 67176767133397189576900993)
  ·
    refine ⟨50382575350047892182675745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67176767133397189576900993 50382575350047892182675745)
    ·
      refine ⟨37786931512535919137006809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50382575350047892182675745 37786931512535919137006809)
      ·
        refine ⟨28340198634401939352755107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37786931512535919137006809 28340198634401939352755107)
        ·
          refine ⟨42510297951602909029132661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28340198634401939352755107 42510297951602909029132661)
          ·
            refine ⟨3985340432962772721481187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42510297951602909029132661 3985340432962772721481187)
            ·
              refine ⟨5978010649444159082221781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3985340432962772721481187 5978010649444159082221781)
              ·
                refine ⟨140109624596347478489573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5978010649444159082221781 140109624596347478489573)
                ·
                  rfl

theorem cell22_3683644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 7].length) (baseStart_3683644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683644 prefixEnd_3683644 := by exact prefixLift 3683644
  have htrace : WordTrace (prefixWord ++ tailWord_3683644) baseStart_3683644 baseEnd_3683644 := by
    simpa [prefixWord, tailWord_3683644, baseEnd_3683644] using wordTrace_append hprefix tailTrace_3683644
  have hstable : (prefixWord ++ tailWord_3683644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683644).length < 2 ^ (prefixWord ++ tailWord_3683644).sum := by decide
  have hdescent : baseEnd_3683644 < baseStart_3683644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683672 : List Nat := [2, 1, 2, 2, 1, 1, 4, 2, 7]
def baseStart_3683672 : Nat := 118140960795 + 3683672 * 2 ^ 59
def prefixEnd_3683672 : Nat := 4983230072969 + 3 ^ 40 * 3683672 * 2
def baseEnd_3683672 : Nat := 420332068779781522235357

theorem tailTrace_3683672 : CollatzResearch.WordTrace tailWord_3683672 prefixEnd_3683672 420332068779781522235357 := by
  unfold tailWord_3683672
  simp only [CollatzResearch.WordTrace]
  refine ⟨67177277755346469967910635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89569703673795293290547513 67177277755346469967910635)
  ·
    refine ⟨100765916633019704951865953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67177277755346469967910635 100765916633019704951865953)
    ·
      refine ⟨75574437474764778713899465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100765916633019704951865953 75574437474764778713899465)
      ·
        refine ⟨56680828106073584035424599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75574437474764778713899465 56680828106073584035424599)
        ·
          refine ⟨85021242159110376053136899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56680828106073584035424599 85021242159110376053136899)
          ·
            refine ⟨127531863238665564079705349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85021242159110376053136899 127531863238665564079705349)
            ·
              refine ⟨23912224357249793264944753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127531863238665564079705349 23912224357249793264944753)
              ·
                refine ⟨17934168267937344948708565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23912224357249793264944753 17934168267937344948708565)
                ·
                  refine ⟨420332068779781522235357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17934168267937344948708565 420332068779781522235357)
                  ·
                    rfl

theorem cell22_3683672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2, 7].length) (baseStart_3683672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683672 prefixEnd_3683672 := by exact prefixLift 3683672
  have htrace : WordTrace (prefixWord ++ tailWord_3683672) baseStart_3683672 baseEnd_3683672 := by
    simpa [prefixWord, tailWord_3683672, baseEnd_3683672] using wordTrace_append hprefix tailTrace_3683672
  have hstable : (prefixWord ++ tailWord_3683672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683672).length < 2 ^ (prefixWord ++ tailWord_3683672).sum := by decide
  have hdescent : baseEnd_3683672 < baseStart_3683672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683693 : List Nat := [1, 5, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_3683693 : Nat := 118140960795 + 3683693 * 2 ^ 59
def prefixEnd_3683693 : Nat := 4983230072969 + 3 ^ 40 * 3683693 * 2
def baseEnd_3683693 : Nat := 1261003395068507511931007

theorem tailTrace_3683693 : CollatzResearch.WordTrace tailWord_3683693 prefixEnd_3683693 1261003395068507511931007 := by
  unfold tailWord_3683693
  simp only [CollatzResearch.WordTrace]
  refine ⟨134355321443616860522335733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89570214295744573681557155 134355321443616860522335733)
  ·
    refine ⟨12595811385339080673968975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134355321443616860522335733 12595811385339080673968975)
    ·
      refine ⟨18893717078008621010953463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12595811385339080673968975 18893717078008621010953463)
      ·
        refine ⟨28340575617012931516430195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18893717078008621010953463 28340575617012931516430195)
        ·
          refine ⟨42510863425519397274645293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28340575617012931516430195 42510863425519397274645293)
          ·
            refine ⟨15941573784569773977991985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42510863425519397274645293 15941573784569773977991985)
            ·
              refine ⟨11956180338427330483493989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15941573784569773977991985 11956180338427330483493989)
              ·
                refine ⟨2241783813455124465655123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11956180338427330483493989 2241783813455124465655123)
                ·
                  refine ⟨3362675720182686698482685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2241783813455124465655123 3362675720182686698482685)
                  ·
                    refine ⟨1261003395068507511931007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3362675720182686698482685 1261003395068507511931007)
                    ·
                      rfl

theorem cell22_3683693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_3683693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683693 prefixEnd_3683693 := by exact prefixLift 3683693
  have htrace : WordTrace (prefixWord ++ tailWord_3683693) baseStart_3683693 baseEnd_3683693 := by
    simpa [prefixWord, tailWord_3683693, baseEnd_3683693] using wordTrace_append hprefix tailTrace_3683693
  have hstable : (prefixWord ++ tailWord_3683693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683693).length < 2 ^ (prefixWord ++ tailWord_3683693).sum := by decide
  have hdescent : baseEnd_3683693 < baseStart_3683693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683796 : List Nat := [2, 4, 1, 2, 4, 9]
def baseStart_3683796 : Nat := 118140960795 + 3683796 * 2 ^ 59
def prefixEnd_3683796 : Nat := 4983230072969 + 3 ^ 40 * 3683796 * 2
def baseEnd_3683796 : Nat := 15568378445351229340811

theorem tailTrace_3683796 : CollatzResearch.WordTrace tailWord_3683796 prefixEnd_3683796 15568378445351229340811 := by
  unfold tailWord_3683796
  simp only [CollatzResearch.WordTrace]
  refine ⟨67179539081121854556667621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89572718774829139408890161 67179539081121854556667621)
  ·
    refine ⟨12596163577710347729375179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67179539081121854556667621 12596163577710347729375179)
    ·
      refine ⟨18894245366565521594062769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12596163577710347729375179 18894245366565521594062769)
      ·
        refine ⟨14170684024924141195547077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18894245366565521594062769 14170684024924141195547077)
        ·
          refine ⟨2657003254673276474165077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14170684024924141195547077 2657003254673276474165077)
          ·
            refine ⟨15568378445351229340811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2657003254673276474165077 15568378445351229340811)
            ·
              rfl

theorem cell22_3683796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 9].length) (baseStart_3683796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683796 prefixEnd_3683796 := by exact prefixLift 3683796
  have htrace : WordTrace (prefixWord ++ tailWord_3683796) baseStart_3683796 baseEnd_3683796 := by
    simpa [prefixWord, tailWord_3683796, baseEnd_3683796] using wordTrace_append hprefix tailTrace_3683796
  have hstable : (prefixWord ++ tailWord_3683796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683796).length < 2 ^ (prefixWord ++ tailWord_3683796).sum := by decide
  have hdescent : baseEnd_3683796 < baseStart_3683796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683798 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_3683798 : Nat := 118140960795 + 3683798 * 2 ^ 59
def prefixEnd_3683798 : Nat := 4983230072969 + 3 ^ 40 * 3683798 * 2
def baseEnd_3683798 : Nat := 1261039338714322238055685

theorem tailTrace_3683798 : CollatzResearch.WordTrace tailWord_3683798 prefixEnd_3683798 1261039338714322238055685 := by
  unfold tailWord_3683798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8397446944264778965931753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89572767405490975636605365 8397446944264778965931753)
  ·
    refine ⟨6298085208198584224448815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8397446944264778965931753 6298085208198584224448815)
    ·
      refine ⟨9447127812297876336673223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6298085208198584224448815 9447127812297876336673223)
      ·
        refine ⟨14170691718446814505009835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9447127812297876336673223 14170691718446814505009835)
        ·
          refine ⟨21256037577670221757514753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14170691718446814505009835 21256037577670221757514753)
          ·
            refine ⟨15942028183252666318136065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21256037577670221757514753 15942028183252666318136065)
            ·
              refine ⟨11956521137439499738602049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15942028183252666318136065 11956521137439499738602049)
              ·
                refine ⟨8967390853079624803951537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11956521137439499738602049 8967390853079624803951537)
                ·
                  refine ⟨6725543139809718602963653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8967390853079624803951537 6725543139809718602963653)
                  ·
                    refine ⟨1261039338714322238055685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6725543139809718602963653 1261039338714322238055685)
                    ·
                      rfl

theorem cell22_3683798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_3683798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683798 prefixEnd_3683798 := by exact prefixLift 3683798
  have htrace : WordTrace (prefixWord ++ tailWord_3683798) baseStart_3683798 baseEnd_3683798 := by
    simpa [prefixWord, tailWord_3683798, baseEnd_3683798] using wordTrace_append hprefix tailTrace_3683798
  have hstable : (prefixWord ++ tailWord_3683798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683798).length < 2 ^ (prefixWord ++ tailWord_3683798).sum := by decide
  have hdescent : baseEnd_3683798 < baseStart_3683798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683809 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 2, 6]
def baseStart_3683809 : Nat := 118140960795 + 3683809 * 2 ^ 59
def prefixEnd_3683809 : Nat := 4983230072969 + 3 ^ 40 * 3683809 * 2
def baseEnd_3683809 : Nat := 1261043104239121876030651

theorem tailTrace_3683809 : CollatzResearch.WordTrace tailWord_3683809 prefixEnd_3683809 1261043104239121876030651 := by
  unfold tailWord_3683809
  simp only [CollatzResearch.WordTrace]
  refine ⟨134359552311196612333558481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89573034874131074889038987 134359552311196612333558481)
  ·
    refine ⟨100769664233397459250168861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134359552311196612333558481 100769664233397459250168861)
    ·
      refine ⟨37788624087524047218813323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100769664233397459250168861 37788624087524047218813323)
      ·
        refine ⟨56682936131286070828219985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37788624087524047218813323 56682936131286070828219985)
        ·
          refine ⟨42512202098464553121164989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56682936131286070828219985 42512202098464553121164989)
          ·
            refine ⟨15942075786924207420436871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42512202098464553121164989 15942075786924207420436871)
            ·
              refine ⟨23913113680386311130655307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15942075786924207420436871 23913113680386311130655307)
              ·
                refine ⟨35869670520579466695982961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23913113680386311130655307 35869670520579466695982961)
                ·
                  refine ⟨26902252890434600021987221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35869670520579466695982961 26902252890434600021987221)
                  ·
                    refine ⟨1261043104239121876030651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26902252890434600021987221 1261043104239121876030651)
                    ·
                      rfl

theorem cell22_3683809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_3683809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683809 prefixEnd_3683809 := by exact prefixLift 3683809
  have htrace : WordTrace (prefixWord ++ tailWord_3683809) baseStart_3683809 baseEnd_3683809 := by
    simpa [prefixWord, tailWord_3683809, baseEnd_3683809] using wordTrace_append hprefix tailTrace_3683809
  have hstable : (prefixWord ++ tailWord_3683809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683809).length < 2 ^ (prefixWord ++ tailWord_3683809).sum := by decide
  have hdescent : baseEnd_3683809 < baseStart_3683809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683903 : List Nat := [1, 1, 2, 2, 3, 3, 3, 3, 4]
def baseStart_3683903 : Nat := 118140960795 + 3683903 * 2 ^ 59
def prefixEnd_3683903 : Nat := 4983230072969 + 3 ^ 40 * 3683903 * 2
def baseEnd_3683903 : Nat := 420358427453378988060121

theorem tailTrace_3683903 : CollatzResearch.WordTrace tailWord_3683903 prefixEnd_3683903 420358427453378988060121 := by
  unfold tailWord_3683903
  simp only [CollatzResearch.WordTrace]
  refine ⟨134362980772856066387480363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89575320515237377591653575 134362980772856066387480363)
  ·
    refine ⟨201544471159284099581220545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134362980772856066387480363 201544471159284099581220545)
    ·
      refine ⟨151158353369463074685915409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201544471159284099581220545 151158353369463074685915409)
      ·
        refine ⟨113368765027097306014436557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151158353369463074685915409 113368765027097306014436557)
        ·
          refine ⟨42513286885161489755413709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113368765027097306014436557 42513286885161489755413709)
          ·
            refine ⟨15942482581935558658280141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42513286885161489755413709 15942482581935558658280141)
            ·
              refine ⟨5978430968225834496855053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15942482581935558658280141 5978430968225834496855053)
              ·
                refine ⟨2241911613084687936320645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5978430968225834496855053 2241911613084687936320645)
                ·
                  refine ⟨420358427453378988060121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2241911613084687936320645 420358427453378988060121)
                  ·
                    rfl

theorem cell22_3683903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 4].length) (baseStart_3683903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683903 prefixEnd_3683903 := by exact prefixLift 3683903
  have htrace : WordTrace (prefixWord ++ tailWord_3683903) baseStart_3683903 baseEnd_3683903 := by
    simpa [prefixWord, tailWord_3683903, baseEnd_3683903] using wordTrace_append hprefix tailTrace_3683903
  have hstable : (prefixWord ++ tailWord_3683903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683903).length < 2 ^ (prefixWord ++ tailWord_3683903).sum := by decide
  have hdescent : baseEnd_3683903 < baseStart_3683903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683916 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 4, 4]
def baseStart_3683916 : Nat := 118140960795 + 3683916 * 2 ^ 59
def prefixEnd_3683916 : Nat := 4983230072969 + 3 ^ 40 * 3683916 * 2
def baseEnd_3683916 : Nat := 1261079732525809263605323

theorem tailTrace_3683916 : CollatzResearch.WordTrace tailWord_3683916 prefixEnd_3683916 1261079732525809263605323 := by
  unfold tailWord_3683916
  simp only [CollatzResearch.WordTrace]
  refine ⟨67181727460904484803851801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89575636614539313071802401 67181727460904484803851801)
  ·
    refine ⟨50386295595678363602888851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67181727460904484803851801 50386295595678363602888851)
    ·
      refine ⟨75579443393517545404333277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50386295595678363602888851 75579443393517545404333277)
      ·
        refine ⟨28342291272569079526624979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75579443393517545404333277 28342291272569079526624979)
        ·
          refine ⟨42513436908853619289937469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28342291272569079526624979 42513436908853619289937469)
          ·
            refine ⟨15942538840820107233726551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42513436908853619289937469 15942538840820107233726551)
            ·
              refine ⟨23913808261230160850589827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15942538840820107233726551 23913808261230160850589827)
              ·
                refine ⟨35870712391845241275884741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23913808261230160850589827 35870712391845241275884741)
                ·
                  refine ⟨6725758573470982739228389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35870712391845241275884741 6725758573470982739228389)
                  ·
                    refine ⟨1261079732525809263605323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6725758573470982739228389 1261079732525809263605323)
                    ·
                      rfl

theorem cell22_3683916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 4, 4].length) (baseStart_3683916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683916 prefixEnd_3683916 := by exact prefixLift 3683916
  have htrace : WordTrace (prefixWord ++ tailWord_3683916) baseStart_3683916 baseEnd_3683916 := by
    simpa [prefixWord, tailWord_3683916, baseEnd_3683916] using wordTrace_append hprefix tailTrace_3683916
  have hstable : (prefixWord ++ tailWord_3683916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683916).length < 2 ^ (prefixWord ++ tailWord_3683916).sum := by decide
  have hdescent : baseEnd_3683916 < baseStart_3683916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683918 : List Nat := [4, 1, 1, 1, 1, 2, 1, 6, 2, 3]
def baseStart_3683918 : Nat := 118140960795 + 3683918 * 2 ^ 59
def prefixEnd_3683918 : Nat := 4983230072969 + 3 ^ 40 * 3683918 * 2
def baseEnd_3683918 : Nat := 1261080417166681925055317

theorem tailTrace_3683918 : CollatzResearch.WordTrace tailWord_3683918 prefixEnd_3683918 1261080417166681925055317 := by
  unfold tailWord_3683918
  simp only [CollatzResearch.WordTrace]
  refine ⟨16795440983475215493659551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89575685245201149299517605 16795440983475215493659551)
  ·
    refine ⟨25193161475212823240489327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16795440983475215493659551 25193161475212823240489327)
    ·
      refine ⟨37789742212819234860733991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25193161475212823240489327 37789742212819234860733991)
      ·
        refine ⟨56684613319228852291100987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37789742212819234860733991 56684613319228852291100987)
        ·
          refine ⟨85026919978843278436651481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56684613319228852291100987 85026919978843278436651481)
          ·
            refine ⟨63770189984132458827488611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85026919978843278436651481 63770189984132458827488611)
            ·
              refine ⟨95655284976198688241232917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63770189984132458827488611 95655284976198688241232917)
              ·
                refine ⟨4483841483259313511307793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95655284976198688241232917 4483841483259313511307793)
                ·
                  refine ⟨3362881112444485133480845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4483841483259313511307793 3362881112444485133480845)
                  ·
                    refine ⟨1261080417166681925055317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3362881112444485133480845 1261080417166681925055317)
                    ·
                      rfl

theorem cell22_3683918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_3683918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683918 prefixEnd_3683918 := by exact prefixLift 3683918
  have htrace : WordTrace (prefixWord ++ tailWord_3683918) baseStart_3683918 baseEnd_3683918 := by
    simpa [prefixWord, tailWord_3683918, baseEnd_3683918] using wordTrace_append hprefix tailTrace_3683918
  have hstable : (prefixWord ++ tailWord_3683918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683918).length < 2 ^ (prefixWord ++ tailWord_3683918).sum := by decide
  have hdescent : baseEnd_3683918 < baseStart_3683918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683926 : List Nat := [5, 2, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3683926 : Nat := 118140960795 + 3683926 * 2 ^ 59
def prefixEnd_3683926 : Nat := 4983230072969 + 3 ^ 40 * 3683926 * 2
def baseEnd_3683926 : Nat := 420361051910057523618431

theorem tailTrace_3683926 : CollatzResearch.WordTrace tailWord_3683926 prefixEnd_3683926 420361051910057523618431 := by
  unfold tailWord_3683926
  simp only [CollatzResearch.WordTrace]
  refine ⟨8397738728235796332222977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89575879767848494210378421 8397738728235796332222977)
  ·
    refine ⟨6298304046176847249167233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8397738728235796332222977 6298304046176847249167233)
    ·
      refine ⟨4723728034632635436875425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6298304046176847249167233 4723728034632635436875425)
      ·
        refine ⟨3542796025974476577656569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4723728034632635436875425 3542796025974476577656569)
        ·
          refine ⟨2657097019480857433242427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3542796025974476577656569 2657097019480857433242427)
          ·
            refine ⟨3985645529221286149863641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657097019480857433242427 3985645529221286149863641)
            ·
              refine ⟨2989234146915964612397731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3985645529221286149863641 2989234146915964612397731)
              ·
                refine ⟨4483851220373946918596597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989234146915964612397731 4483851220373946918596597)
                ·
                  refine ⟨420361051910057523618431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4483851220373946918596597 420361051910057523618431)
                  ·
                    rfl

theorem cell22_3683926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3683926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683926 prefixEnd_3683926 := by exact prefixLift 3683926
  have htrace : WordTrace (prefixWord ++ tailWord_3683926) baseStart_3683926 baseEnd_3683926 := by
    simpa [prefixWord, tailWord_3683926, baseEnd_3683926] using wordTrace_append hprefix tailTrace_3683926
  have hstable : (prefixWord ++ tailWord_3683926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683926).length < 2 ^ (prefixWord ++ tailWord_3683926).sum := by decide
  have hdescent : baseEnd_3683926 < baseStart_3683926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683950 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_3683950 : Nat := 118140960795 + 3683950 * 2 ^ 59
def prefixEnd_3683950 : Nat := 4983230072969 + 3 ^ 40 * 3683950 * 2
def baseEnd_3683950 : Nat := 1261091371420644508255219

theorem tailTrace_3683950 : CollatzResearch.WordTrace tailWord_3683950 prefixEnd_3683950 1261091371420644508255219 := by
  unfold tailWord_3683950
  simp only [CollatzResearch.WordTrace]
  refine ⟨16795586875460724176805163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89576463335790528942960869 16795586875460724176805163)
  ·
    refine ⟨25193380313191086265207745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16795586875460724176805163 25193380313191086265207745)
    ·
      refine ⟨18895035234893314698905809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25193380313191086265207745 18895035234893314698905809)
      ·
        refine ⟨14171276426169986024179357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18895035234893314698905809 14171276426169986024179357)
        ·
          refine ⟨5314228659813744759067259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14171276426169986024179357 5314228659813744759067259)
          ·
            refine ⟨7971342989720617138600889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5314228659813744759067259 7971342989720617138600889)
            ·
              refine ⟨5978507242290462853950667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7971342989720617138600889 5978507242290462853950667)
              ·
                refine ⟨8967760863435694280926001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5978507242290462853950667 8967760863435694280926001)
                ·
                  refine ⟨6725820647576770710694501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8967760863435694280926001 6725820647576770710694501)
                  ·
                    refine ⟨1261091371420644508255219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6725820647576770710694501 1261091371420644508255219)
                    ·
                      rfl

theorem cell22_3683950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_3683950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683950 prefixEnd_3683950 := by exact prefixLift 3683950
  have htrace : WordTrace (prefixWord ++ tailWord_3683950) baseStart_3683950 baseEnd_3683950 := by
    simpa [prefixWord, tailWord_3683950, baseEnd_3683950] using wordTrace_append hprefix tailTrace_3683950
  have hstable : (prefixWord ++ tailWord_3683950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683950).length < 2 ^ (prefixWord ++ tailWord_3683950).sum := by decide
  have hdescent : baseEnd_3683950 < baseStart_3683950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683980 : List Nat := [2, 2, 1, 2, 1, 1, 5, 4, 1, 3]
def baseStart_3683980 : Nat := 118140960795 + 3683980 * 2 ^ 59
def prefixEnd_3683980 : Nat := 4983230072969 + 3 ^ 40 * 3683980 * 2
def baseEnd_3683980 : Nat := 1261101641033734430005127

theorem tailTrace_3683980 : CollatzResearch.WordTrace tailWord_3683980 prefixEnd_3683980 1261101641033734430005127 := by
  unfold tailWord_3683980
  simp only [CollatzResearch.WordTrace]
  refine ⟨67182894596788554269016697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89577192795718072358688929 67182894596788554269016697)
  ·
    refine ⟨50387170947591415701762523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67182894596788554269016697 50387170947591415701762523)
    ·
      refine ⟨75580756421387123552643785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50387170947591415701762523 75580756421387123552643785)
      ·
        refine ⟨56685567316040342664482839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75580756421387123552643785 56685567316040342664482839)
        ·
          refine ⟨85028350974060513996724259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56685567316040342664482839 85028350974060513996724259)
          ·
            refine ⟨127542526461090770995086389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85028350974060513996724259 127542526461090770995086389)
            ·
              refine ⟨11957111855727259780789349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127542526461090770995086389 11957111855727259780789349)
              ·
                refine ⟨2241958472948861208898003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11957111855727259780789349 2241958472948861208898003)
                ·
                  refine ⟨3362937709423291813347005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2241958472948861208898003 3362937709423291813347005)
                  ·
                    refine ⟨1261101641033734430005127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3362937709423291813347005 1261101641033734430005127)
                    ·
                      rfl

theorem cell22_3683980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_3683980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683980 prefixEnd_3683980 := by exact prefixLift 3683980
  have htrace : WordTrace (prefixWord ++ tailWord_3683980) baseStart_3683980 baseEnd_3683980 := by
    simpa [prefixWord, tailWord_3683980, baseEnd_3683980] using wordTrace_append hprefix tailTrace_3683980
  have hstable : (prefixWord ++ tailWord_3683980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683980).length < 2 ^ (prefixWord ++ tailWord_3683980).sum := by decide
  have hdescent : baseEnd_3683980 < baseStart_3683980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3683991 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 1, 7]
def baseStart_3683991 : Nat := 118140960795 + 3683991 * 2 ^ 59
def prefixEnd_3683991 : Nat := 4983230072969 + 3 ^ 40 * 3683991 * 2
def baseEnd_3683991 : Nat := 1261105406558534067980093

theorem tailTrace_3683991 : CollatzResearch.WordTrace tailWord_3683991 prefixEnd_3683991 1261105406558534067980093 := by
  unfold tailWord_3683991
  simp only [CollatzResearch.WordTrace]
  refine ⟨134366190396537257416683827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89577460264358171611122551 134366190396537257416683827)
  ·
    refine ⟨201549285594805886125025741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134366190396537257416683827 201549285594805886125025741)
    ·
      refine ⟨75580982098052207296884653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201549285594805886125025741 75580982098052207296884653)
      ·
        refine ⟨28342868286769577736331745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75580982098052207296884653 28342868286769577736331745)
        ·
          refine ⟨21257151215077183302248809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28342868286769577736331745 21257151215077183302248809)
          ·
            refine ⟨15942863411307887476686607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21257151215077183302248809 15942863411307887476686607)
            ·
              refine ⟨23914295116961831215029911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15942863411307887476686607 23914295116961831215029911)
              ·
                refine ⟨35871442675442746822544867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23914295116961831215029911 35871442675442746822544867)
                ·
                  refine ⟨53807164013164120233817301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35871442675442746822544867 53807164013164120233817301)
                  ·
                    refine ⟨1261105406558534067980093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53807164013164120233817301 1261105406558534067980093)
                    ·
                      rfl

theorem cell22_3683991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_3683991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3683991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3683991 prefixEnd_3683991 := by exact prefixLift 3683991
  have htrace : WordTrace (prefixWord ++ tailWord_3683991) baseStart_3683991 baseEnd_3683991 := by
    simpa [prefixWord, tailWord_3683991, baseEnd_3683991] using wordTrace_append hprefix tailTrace_3683991
  have hstable : (prefixWord ++ tailWord_3683991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3683991).length < 2 ^ (prefixWord ++ tailWord_3683991).sum := by decide
  have hdescent : baseEnd_3683991 < baseStart_3683991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3683991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684068 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 2, 4]
def baseStart_3684068 : Nat := 118140960795 + 3684068 * 2 ^ 59
def prefixEnd_3684068 : Nat := 4983230072969 + 3 ^ 40 * 3684068 * 2
def baseEnd_3684068 : Nat := 1261131765232131533804857

theorem tailTrace_3684068 : CollatzResearch.WordTrace tailWord_3684068 prefixEnd_3684068 1261131765232131533804857 := by
  unfold tailWord_3684068
  simp only [CollatzResearch.WordTrace]
  refine ⟨67184499408629149783618429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89579332544838866378157905 67184499408629149783618429)
  ·
    refine ⟨25194187278235931168856911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67184499408629149783618429 25194187278235931168856911)
    ·
      refine ⟨37791280917353896753285367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25194187278235931168856911 37791280917353896753285367)
      ·
        refine ⟨56686921376030845129928051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37791280917353896753285367 56686921376030845129928051)
        ·
          refine ⟨85030382064046267694892077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56686921376030845129928051 85030382064046267694892077)
          ·
            refine ⟨31886393274017350385584529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85030382064046267694892077 31886393274017350385584529)
            ·
              refine ⟨23914794955513012789188397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31886393274017350385584529 23914794955513012789188397)
              ·
                refine ⟨8968048108317379795945649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23914794955513012789188397 8968048108317379795945649)
                ·
                  refine ⟨6726036081238034846959237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8968048108317379795945649 6726036081238034846959237)
                  ·
                    refine ⟨1261131765232131533804857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6726036081238034846959237 1261131765232131533804857)
                    ·
                      rfl

theorem cell22_3684068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_3684068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684068 prefixEnd_3684068 := by exact prefixLift 3684068
  have htrace : WordTrace (prefixWord ++ tailWord_3684068) baseStart_3684068 baseEnd_3684068 := by
    simpa [prefixWord, tailWord_3684068, baseEnd_3684068] using wordTrace_append hprefix tailTrace_3684068
  have hstable : (prefixWord ++ tailWord_3684068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684068).length < 2 ^ (prefixWord ++ tailWord_3684068).sum := by decide
  have hdescent : baseEnd_3684068 < baseStart_3684068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684072 : List Nat := [2, 1, 4, 1, 3, 3, 1, 3, 4]
def baseStart_3684072 : Nat := 118140960795 + 3684072 * 2 ^ 59
def prefixEnd_3684072 : Nat := 4983230072969 + 3 ^ 40 * 3684072 * 2
def baseEnd_3684072 : Nat := 420377711504625618901615

theorem tailTrace_3684072 : CollatzResearch.WordTrace tailWord_3684072 prefixEnd_3684072 420377711504625618901615 := by
  unfold tailWord_3684072
  simp only [CollatzResearch.WordTrace]
  refine ⟨67184572354621904125191235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89579429806162538833588313 67184572354621904125191235)
  ·
    refine ⟨100776858531932856187786853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67184572354621904125191235 100776858531932856187786853)
    ·
      refine ⟨18895660974737410535210035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100776858531932856187786853 18895660974737410535210035)
      ·
        refine ⟨28343491462106115802815053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18895660974737410535210035 28343491462106115802815053)
        ·
          refine ⟨10628809298289793426055645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28343491462106115802815053 10628809298289793426055645)
          ·
            refine ⟨3985803486858672534770867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10628809298289793426055645 3985803486858672534770867)
            ·
              refine ⟨5978705230288008802156301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3985803486858672534770867 5978705230288008802156301)
              ·
                refine ⟨2242014461358003300808613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5978705230288008802156301 2242014461358003300808613)
                ·
                  refine ⟨420377711504625618901615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2242014461358003300808613 420377711504625618901615)
                  ·
                    rfl

theorem cell22_3684072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 4].length) (baseStart_3684072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684072 prefixEnd_3684072 := by exact prefixLift 3684072
  have htrace : WordTrace (prefixWord ++ tailWord_3684072) baseStart_3684072 baseEnd_3684072 := by
    simpa [prefixWord, tailWord_3684072, baseEnd_3684072] using wordTrace_append hprefix tailTrace_3684072
  have hstable : (prefixWord ++ tailWord_3684072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684072).length < 2 ^ (prefixWord ++ tailWord_3684072).sum := by decide
  have hdescent : baseEnd_3684072 < baseStart_3684072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684096 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 1, 8]
def baseStart_3684096 : Nat := 118140960795 + 3684096 * 2 ^ 59
def prefixEnd_3684096 : Nat := 4983230072969 + 3 ^ 40 * 3684096 * 2
def baseEnd_3684096 : Nat := 1261141350204348794104771

theorem tailTrace_3684096 : CollatzResearch.WordTrace tailWord_3684096 prefixEnd_3684096 1261141350204348794104771 := by
  unfold tailWord_3684096
  simp only [CollatzResearch.WordTrace]
  refine ⟨67185010030578430174628071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89580013374104573566170761 67185010030578430174628071)
  ·
    refine ⟨100777515045867645261942107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67185010030578430174628071 100777515045867645261942107)
    ·
      refine ⟨151166272568801467892913161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100777515045867645261942107 151166272568801467892913161)
      ·
        refine ⟨113374704426601100919684871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151166272568801467892913161 113374704426601100919684871)
        ·
          refine ⟨170062056639901651379527307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113374704426601100919684871 170062056639901651379527307)
          ·
            refine ⟨255093084959852477069290961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170062056639901651379527307 255093084959852477069290961)
            ·
              refine ⟨191319813719889357801968221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 255093084959852477069290961 191319813719889357801968221)
              ·
                refine ⟨71744930144958509175738083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191319813719889357801968221 71744930144958509175738083)
                ·
                  refine ⟨107617395217437763763607125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71744930144958509175738083 107617395217437763763607125)
                  ·
                    refine ⟨1261141350204348794104771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107617395217437763763607125 1261141350204348794104771)
                    ·
                      rfl

theorem cell22_3684096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_3684096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684096 prefixEnd_3684096 := by exact prefixLift 3684096
  have htrace : WordTrace (prefixWord ++ tailWord_3684096) baseStart_3684096 baseEnd_3684096 := by
    simpa [prefixWord, tailWord_3684096, baseEnd_3684096] using wordTrace_append hprefix tailTrace_3684096
  have hstable : (prefixWord ++ tailWord_3684096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684096).length < 2 ^ (prefixWord ++ tailWord_3684096).sum := by decide
  have hdescent : baseEnd_3684096 < baseStart_3684096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684111 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 9]
def baseStart_3684111 : Nat := 118140960795 + 3684111 * 2 ^ 59
def prefixEnd_3684111 : Nat := 4983230072969 + 3 ^ 40 * 3684111 * 2
def baseEnd_3684111 : Nat := 420382161670297918326575

theorem tailTrace_3684111 : CollatzResearch.WordTrace tailWord_3684111 prefixEnd_3684111 420382161670297918326575 := by
  unfold tailWord_3684111
  simp only [CollatzResearch.WordTrace]
  refine ⟨134370567156102517911052187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89580378104068345274034791 134370567156102517911052187)
  ·
    refine ⟨201555850734153776866578281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134370567156102517911052187 201555850734153776866578281)
    ·
      refine ⟨151166888050615332649933711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201555850734153776866578281 151166888050615332649933711)
      ·
        refine ⟨226750332075922998974900567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151166888050615332649933711 226750332075922998974900567)
        ·
          refine ⟨340125498113884498462350851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226750332075922998974900567 340125498113884498462350851)
          ·
            refine ⟨510188247170826747693526277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340125498113884498462350851 510188247170826747693526277)
            ·
              refine ⟨95660296344530015192536177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 510188247170826747693526277 95660296344530015192536177)
              ·
                refine ⟨71745222258397511394402133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95660296344530015192536177 71745222258397511394402133)
                ·
                  refine ⟨420382161670297918326575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71745222258397511394402133 420382161670297918326575)
                  ·
                    rfl

theorem cell22_3684111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 9].length) (baseStart_3684111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684111 prefixEnd_3684111 := by exact prefixLift 3684111
  have htrace : WordTrace (prefixWord ++ tailWord_3684111) baseStart_3684111 baseEnd_3684111 := by
    simpa [prefixWord, tailWord_3684111, baseEnd_3684111] using wordTrace_append hprefix tailTrace_3684111
  have hstable : (prefixWord ++ tailWord_3684111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684111).length < 2 ^ (prefixWord ++ tailWord_3684111).sum := by decide
  have hdescent : baseEnd_3684111 < baseStart_3684111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684145 : List Nat := [1, 2, 2, 3, 2, 3, 2, 2, 5]
def baseStart_3684145 : Nat := 118140960795 + 3684145 * 2 ^ 59
def prefixEnd_3684145 : Nat := 4983230072969 + 3 ^ 40 * 3684145 * 2
def baseEnd_3684145 : Nat := 420386041301909666543207

theorem tailTrace_3684145 : CollatzResearch.WordTrace tailWord_3684145 prefixEnd_3684145 420386041301909666543207 := by
  unfold tailWord_3684145
  simp only [CollatzResearch.WordTrace]
  refine ⟨134371807237979341717789889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89581204825319561145193259 134371807237979341717789889)
  ·
    refine ⟨100778855428484506288342417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134371807237979341717789889 100778855428484506288342417)
    ·
      refine ⟨75584141571363379716256813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100778855428484506288342417 75584141571363379716256813)
      ·
        refine ⟨28344053089261267393596305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75584141571363379716256813 28344053089261267393596305)
        ·
          refine ⟨21258039816945950545197229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28344053089261267393596305 21258039816945950545197229)
          ·
            refine ⟨7971764931354731454448961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21258039816945950545197229 7971764931354731454448961)
            ·
              refine ⟨5978823698516048590836721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7971764931354731454448961 5978823698516048590836721)
              ·
                refine ⟨4484117773887036443127541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5978823698516048590836721 4484117773887036443127541)
                ·
                  refine ⟨420386041301909666543207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4484117773887036443127541 420386041301909666543207)
                  ·
                    rfl

theorem cell22_3684145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 5].length) (baseStart_3684145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684145 prefixEnd_3684145 := by exact prefixLift 3684145
  have htrace : WordTrace (prefixWord ++ tailWord_3684145) baseStart_3684145 baseEnd_3684145 := by
    simpa [prefixWord, tailWord_3684145, baseEnd_3684145] using wordTrace_append hprefix tailTrace_3684145
  have hstable : (prefixWord ++ tailWord_3684145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684145).length < 2 ^ (prefixWord ++ tailWord_3684145).sum := by decide
  have hdescent : baseEnd_3684145 < baseStart_3684145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684149 : List Nat := [1, 3, 3, 1, 4, 1, 1, 4, 1, 3]
def baseStart_3684149 : Nat := 118140960795 + 3684149 * 2 ^ 59
def prefixEnd_3684149 : Nat := 4983230072969 + 3 ^ 40 * 3684149 * 2
def baseEnd_3684149 : Nat := 1261159493187474322529609

theorem tailTrace_3684149 : CollatzResearch.WordTrace tailWord_3684149 prefixEnd_3684149 1261159493187474322529609 := by
  unfold tailWord_3684149
  simp only [CollatzResearch.WordTrace]
  refine ⟨134371953129964850400935501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89581302086643233600623667 134371953129964850400935501)
  ·
    refine ⟨50389482423736818900350813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134371953129964850400935501 50389482423736818900350813)
    ·
      refine ⟨18896055908901307087631555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50389482423736818900350813 18896055908901307087631555)
      ·
        refine ⟨28344083863351960631447333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18896055908901307087631555 28344083863351960631447333)
        ·
          refine ⟨5314515724378492618396375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28344083863351960631447333 5314515724378492618396375)
          ·
            refine ⟨7971773586567738927594563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5314515724378492618396375 7971773586567738927594563)
            ·
              refine ⟨11957660379851608391391845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7971773586567738927594563 11957660379851608391391845)
              ·
                refine ⟨2242061321222176573385971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11957660379851608391391845 2242061321222176573385971)
                ·
                  refine ⟨3363091981833264860078957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242061321222176573385971 3363091981833264860078957)
                  ·
                    refine ⟨1261159493187474322529609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3363091981833264860078957 1261159493187474322529609)
                    ·
                      rfl

theorem cell22_3684149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_3684149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684149 prefixEnd_3684149 := by exact prefixLift 3684149
  have htrace : WordTrace (prefixWord ++ tailWord_3684149) baseStart_3684149 baseEnd_3684149 := by
    simpa [prefixWord, tailWord_3684149, baseEnd_3684149] using wordTrace_append hprefix tailTrace_3684149
  have hstable : (prefixWord ++ tailWord_3684149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684149).length < 2 ^ (prefixWord ++ tailWord_3684149).sum := by decide
  have hdescent : baseEnd_3684149 < baseStart_3684149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684192 : List Nat := [2, 1, 1, 3, 3, 2, 4, 1, 1, 4]
def baseStart_3684192 : Nat := 118140960795 + 3684192 * 2 ^ 59
def prefixEnd_3684192 : Nat := 4983230072969 + 3 ^ 40 * 3684192 * 2
def baseEnd_3684192 : Nat := 1261174212966236543704477

theorem tailTrace_3684192 : CollatzResearch.WordTrace tailWord_3684192 prefixEnd_3684192 1261174212966236543704477 := by
  unfold tailWord_3684192
  simp only [CollatzResearch.WordTrace]
  refine ⟨67186760734404534372375415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89582347645872712496500553 67186760734404534372375415)
  ·
    refine ⟨100780141101606801558563123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67186760734404534372375415 100780141101606801558563123)
    ·
      refine ⟨151170211652410202337844685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100780141101606801558563123 151170211652410202337844685)
      ·
        refine ⟨56688829369653825876691757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151170211652410202337844685 56688829369653825876691757)
        ·
          refine ⟨21258311013620184703759409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56688829369653825876691757 21258311013620184703759409)
          ·
            refine ⟨15943733260215138527819557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21258311013620184703759409 15943733260215138527819557)
            ·
              refine ⟨2989449986290338473966167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15943733260215138527819557 2989449986290338473966167)
              ·
                refine ⟨4484174979435507710949251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989449986290338473966167 4484174979435507710949251)
                ·
                  refine ⟨6726262469153261566423877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4484174979435507710949251 6726262469153261566423877)
                  ·
                    refine ⟨1261174212966236543704477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6726262469153261566423877 1261174212966236543704477)
                    ·
                      rfl

theorem cell22_3684192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 1, 4].length) (baseStart_3684192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684192 prefixEnd_3684192 := by exact prefixLift 3684192
  have htrace : WordTrace (prefixWord ++ tailWord_3684192) baseStart_3684192 baseEnd_3684192 := by
    simpa [prefixWord, tailWord_3684192, baseEnd_3684192] using wordTrace_append hprefix tailTrace_3684192
  have hstable : (prefixWord ++ tailWord_3684192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684192).length < 2 ^ (prefixWord ++ tailWord_3684192).sum := by decide
  have hdescent : baseEnd_3684192 < baseStart_3684192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684203 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 4, 4]
def baseStart_3684203 : Nat := 118140960795 + 3684203 * 2 ^ 59
def prefixEnd_3684203 : Nat := 4983230072969 + 3 ^ 40 * 3684203 * 2
def baseEnd_3684203 : Nat := 1261177978491036181679443

theorem tailTrace_3684203 : CollatzResearch.WordTrace tailWord_3684203 prefixEnd_3684203 1261177978491036181679443 := by
  unfold tailWord_3684203
  simp only [CollatzResearch.WordTrace]
  refine ⟨134373922671769217623401263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89582615114512811748934175 134373922671769217623401263)
  ·
    refine ⟨201560884007653826435101895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134373922671769217623401263 201560884007653826435101895)
    ·
      refine ⟨302341326011480739652652843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201560884007653826435101895 302341326011480739652652843)
      ·
        refine ⟨453511989017221109478979265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302341326011480739652652843 453511989017221109478979265)
        ·
          refine ⟨340133991762915832109234449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 453511989017221109478979265 340133991762915832109234449)
          ·
            refine ⟨255100493822186874081925837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340133991762915832109234449 255100493822186874081925837)
            ·
              refine ⟨95662685183320077780722189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 255100493822186874081925837 95662685183320077780722189)
              ·
                refine ⟨35873506943745029167770821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95662685183320077780722189 35873506943745029167770821)
                ·
                  refine ⟨6726282551952192968957029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35873506943745029167770821 6726282551952192968957029)
                  ·
                    refine ⟨1261177978491036181679443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6726282551952192968957029 1261177978491036181679443)
                    ·
                      rfl

theorem cell22_3684203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 4].length) (baseStart_3684203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684203 prefixEnd_3684203 := by exact prefixLift 3684203
  have htrace : WordTrace (prefixWord ++ tailWord_3684203) baseStart_3684203 baseEnd_3684203 := by
    simpa [prefixWord, tailWord_3684203, baseEnd_3684203] using wordTrace_append hprefix tailTrace_3684203
  have hstable : (prefixWord ++ tailWord_3684203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684203).length < 2 ^ (prefixWord ++ tailWord_3684203).sum := by decide
  have hdescent : baseEnd_3684203 < baseStart_3684203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684233 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 2, 7]
def baseStart_3684233 : Nat := 118140960795 + 3684233 * 2 ^ 59
def prefixEnd_3684233 : Nat := 4983230072969 + 3 ^ 40 * 3684233 * 2
def baseEnd_3684233 : Nat := 1261188248104126103429351

theorem tailTrace_3684233 : CollatzResearch.WordTrace tailWord_3684233 prefixEnd_3684233 1261188248104126103429351 := by
  unfold tailWord_3684233
  simp only [CollatzResearch.WordTrace]
  refine ⟨134375016861660532746993353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89583344574440355164662235 134375016861660532746993353)
  ·
    refine ⟨100781262646245399560245015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134375016861660532746993353 100781262646245399560245015)
    ·
      refine ⟨151171893969368099340367523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100781262646245399560245015 151171893969368099340367523)
      ·
        refine ⟨226757840954052149010551285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151171893969368099340367523 226757840954052149010551285)
        ·
          refine ⟨21258547589442388969739183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226757840954052149010551285 21258547589442388969739183)
          ·
            refine ⟨31887821384163583454608775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21258547589442388969739183 31887821384163583454608775)
            ·
              refine ⟨47831732076245375181913163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31887821384163583454608775 47831732076245375181913163)
              ·
                refine ⟨71747598114368062772869745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47831732076245375181913163 71747598114368062772869745)
                ·
                  refine ⟨53810698585776047079652309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71747598114368062772869745 53810698585776047079652309)
                  ·
                    refine ⟨1261188248104126103429351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53810698585776047079652309 1261188248104126103429351)
                    ·
                      rfl

theorem cell22_3684233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_3684233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684233 prefixEnd_3684233 := by exact prefixLift 3684233
  have htrace : WordTrace (prefixWord ++ tailWord_3684233) baseStart_3684233 baseEnd_3684233 := by
    simpa [prefixWord, tailWord_3684233, baseEnd_3684233] using wordTrace_append hprefix tailTrace_3684233
  have hstable : (prefixWord ++ tailWord_3684233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684233).length < 2 ^ (prefixWord ++ tailWord_3684233).sum := by decide
  have hdescent : baseEnd_3684233 < baseStart_3684233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684280 : List Nat := [2, 1, 2, 1, 2, 3, 3, 3, 5]
def baseStart_3684280 : Nat := 118140960795 + 3684280 * 2 ^ 59
def prefixEnd_3684280 : Nat := 4983230072969 + 3 ^ 40 * 3684280 * 2
def baseEnd_3684280 : Nat := 420401445721544549168069

theorem tailTrace_3684280 : CollatzResearch.WordTrace tailWord_3684280 prefixEnd_3684280 420401445721544549168069 := by
  unfold tailWord_3684280
  simp only [CollatzResearch.WordTrace]
  refine ⟨67188365546245129886977147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89584487394993506515969529 67188365546245129886977147)
  ·
    refine ⟨100782548319367694830465721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67188365546245129886977147 100782548319367694830465721)
    ·
      refine ⟨75586911239525771122849291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100782548319367694830465721 75586911239525771122849291)
      ·
        refine ⟨113380366859288656684273937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75586911239525771122849291 113380366859288656684273937)
        ·
          refine ⟨85035275144466492513205453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113380366859288656684273937 85035275144466492513205453)
          ·
            refine ⟨31888228179174934692452045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85035275144466492513205453 31888228179174934692452045)
            ·
              refine ⟨11958085567190600509669517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31888228179174934692452045 11958085567190600509669517)
              ·
                refine ⟨4484282087696475191126069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11958085567190600509669517 4484282087696475191126069)
                ·
                  refine ⟨420401445721544549168069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4484282087696475191126069 420401445721544549168069)
                  ·
                    rfl

theorem cell22_3684280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 3, 5].length) (baseStart_3684280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684280 prefixEnd_3684280 := by exact prefixLift 3684280
  have htrace : WordTrace (prefixWord ++ tailWord_3684280) baseStart_3684280 baseEnd_3684280 := by
    simpa [prefixWord, tailWord_3684280, baseEnd_3684280] using wordTrace_append hprefix tailTrace_3684280
  have hstable : (prefixWord ++ tailWord_3684280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684280).length < 2 ^ (prefixWord ++ tailWord_3684280).sum := by decide
  have hdescent : baseEnd_3684280 < baseStart_3684280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684359 : List Nat := [1, 1, 4, 3, 1, 3, 2, 3, 4]
def baseStart_3684359 : Nat := 118140960795 + 3684359 * 2 ^ 59
def prefixEnd_3684359 : Nat := 4983230072969 + 3 ^ 40 * 3684359 * 2
def baseEnd_3684359 : Nat := 420410460159701258259655

theorem tailTrace_3684359 : CollatzResearch.WordTrace tailWord_3684359 prefixEnd_3684359 420410460159701258259655 := by
  unfold tailWord_3684359
  simp only [CollatzResearch.WordTrace]
  refine ⟨134379612459204056266080131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89586408306136037510720087 134379612459204056266080131)
  ·
    refine ⟨201569418688806084399120197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134379612459204056266080131 201569418688806084399120197)
    ·
      refine ⟨37794266004151140824835037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201569418688806084399120197 37794266004151140824835037)
      ·
        refine ⟨14172849751556677809313139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37794266004151140824835037 14172849751556677809313139)
        ·
          refine ⟨21259274627335016713969709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14172849751556677809313139 21259274627335016713969709)
          ·
            refine ⟨7972227985250631267738641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21259274627335016713969709 7972227985250631267738641)
            ·
              refine ⟨5979170988937973450803981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7972227985250631267738641 5979170988937973450803981)
              ·
                refine ⟨2242189120851740044051493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5979170988937973450803981 2242189120851740044051493)
                ·
                  refine ⟨420410460159701258259655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2242189120851740044051493 420410460159701258259655)
                  ·
                    rfl

theorem cell22_3684359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 4].length) (baseStart_3684359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684359 prefixEnd_3684359 := by exact prefixLift 3684359
  have htrace : WordTrace (prefixWord ++ tailWord_3684359) baseStart_3684359 baseEnd_3684359 := by
    simpa [prefixWord, tailWord_3684359, baseEnd_3684359] using wordTrace_append hprefix tailTrace_3684359
  have hstable : (prefixWord ++ tailWord_3684359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684359).length < 2 ^ (prefixWord ++ tailWord_3684359).sum := by decide
  have hdescent : baseEnd_3684359 < baseStart_3684359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684365 : List Nat := [1, 7, 1, 2, 2, 1, 1, 2, 5]
def baseStart_3684365 : Nat := 118140960795 + 3684365 * 2 ^ 59
def prefixEnd_3684365 : Nat := 4983230072969 + 3 ^ 40 * 3684365 * 2
def baseEnd_3684365 : Nat := 420411144800573919709649

theorem tailTrace_3684365 : CollatzResearch.WordTrace tailWord_3684365 prefixEnd_3684365 420411144800573919709649 := by
  unfold tailWord_3684365
  simp only [CollatzResearch.WordTrace]
  refine ⟨134379831297182319290798549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89586554198121546193865699 134379831297182319290798549)
  ·
    refine ⟨3149527296027710608378091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 134379831297182319290798549 3149527296027710608378091)
    ·
      refine ⟨4724290944041565912567137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3149527296027710608378091 4724290944041565912567137)
      ·
        refine ⟨3543218208031174434425353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4724290944041565912567137 3543218208031174434425353)
        ·
          refine ⟨2657413656023380825819015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3543218208031174434425353 2657413656023380825819015)
          ·
            refine ⟨3986120484035071238728523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2657413656023380825819015 3986120484035071238728523)
            ·
              refine ⟨5979180726052606858092785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3986120484035071238728523 5979180726052606858092785)
              ·
                refine ⟨4484385544539455143569589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5979180726052606858092785 4484385544539455143569589)
                ·
                  refine ⟨420411144800573919709649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4484385544539455143569589 420411144800573919709649)
                  ·
                    rfl

theorem cell22_3684365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_3684365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684365 prefixEnd_3684365 := by exact prefixLift 3684365
  have htrace : WordTrace (prefixWord ++ tailWord_3684365) baseStart_3684365 baseEnd_3684365 := by
    simpa [prefixWord, tailWord_3684365, baseEnd_3684365] using wordTrace_append hprefix tailTrace_3684365
  have hstable : (prefixWord ++ tailWord_3684365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684365).length < 2 ^ (prefixWord ++ tailWord_3684365).sum := by decide
  have hdescent : baseEnd_3684365 < baseStart_3684365 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684391 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 1, 5]
def baseStart_3684391 : Nat := 118140960795 + 3684391 * 2 ^ 59
def prefixEnd_3684391 : Nat := 4983230072969 + 3 ^ 40 * 3684391 * 2
def baseEnd_3684391 : Nat := 1261242334733066357978867

theorem tailTrace_3684391 : CollatzResearch.WordTrace tailWord_3684391 prefixEnd_3684391 1261242334733066357978867 := by
  unfold tailWord_3684391
  simp only [CollatzResearch.WordTrace]
  refine ⟨134380779595088125731245027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89587186396725417154163351 134380779595088125731245027)
  ·
    refine ⟨201571169392632188596867541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134380779595088125731245027 201571169392632188596867541)
    ·
      refine ⟨4724324282639816920239083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 201571169392632188596867541 4724324282639816920239083)
      ·
        refine ⟨7086486423959725380358625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4724324282639816920239083 7086486423959725380358625)
        ·
          refine ⟨5314864817969794035268969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7086486423959725380358625 5314864817969794035268969)
          ·
            refine ⟨3986148613477345526451727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5314864817969794035268969 3986148613477345526451727)
            ·
              refine ⟨5979222920216018289677591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3986148613477345526451727 5979222920216018289677591)
              ·
                refine ⟨8968834380324027434516387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5979222920216018289677591 8968834380324027434516387)
                ·
                  refine ⟨13453251570486041151774581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8968834380324027434516387 13453251570486041151774581)
                  ·
                    refine ⟨1261242334733066357978867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13453251570486041151774581 1261242334733066357978867)
                    ·
                      rfl

theorem cell22_3684391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_3684391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684391 prefixEnd_3684391 := by exact prefixLift 3684391
  have htrace : WordTrace (prefixWord ++ tailWord_3684391) baseStart_3684391 baseEnd_3684391 := by
    simpa [prefixWord, tailWord_3684391, baseEnd_3684391] using wordTrace_append hprefix tailTrace_3684391
  have hstable : (prefixWord ++ tailWord_3684391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684391).length < 2 ^ (prefixWord ++ tailWord_3684391).sum := by decide
  have hdescent : baseEnd_3684391 < baseStart_3684391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684404 : List Nat := [2, 5, 1, 2, 2, 1, 1, 8]
def baseStart_3684404 : Nat := 118140960795 + 3684404 * 2 ^ 59
def prefixEnd_3684404 : Nat := 4983230072969 + 3 ^ 40 * 3684404 * 2
def baseEnd_3684404 : Nat := 140138531655415406378203

theorem tailTrace_3684404 : CollatzResearch.WordTrace tailWord_3684404 prefixEnd_3684404 140138531655415406378203 := by
  unfold tailWord_3684404
  simp only [CollatzResearch.WordTrace]
  refine ⟨67190626872020514475734133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89587502496027352634312177 67190626872020514475734133)
  ·
    refine ⟨6299121269251923232100075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67190626872020514475734133 6299121269251923232100075)
    ·
      refine ⟨9448681903877884848150113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6299121269251923232100075 9448681903877884848150113)
      ·
        refine ⟨7086511427908413636112585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9448681903877884848150113 7086511427908413636112585)
        ·
          refine ⟨5314883570931310227084439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7086511427908413636112585 5314883570931310227084439)
          ·
            refine ⟨7972325356396965340626659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5314883570931310227084439 7972325356396965340626659)
            ·
              refine ⟨11958488034595448010939989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7972325356396965340626659 11958488034595448010939989)
              ·
                refine ⟨140138531655415406378203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11958488034595448010939989 140138531655415406378203)
                ·
                  rfl

theorem cell22_3684404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 8].length) (baseStart_3684404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684404 prefixEnd_3684404 := by exact prefixLift 3684404
  have htrace : WordTrace (prefixWord ++ tailWord_3684404) baseStart_3684404 baseEnd_3684404 := by
    simpa [prefixWord, tailWord_3684404, baseEnd_3684404] using wordTrace_append hprefix tailTrace_3684404
  have hstable : (prefixWord ++ tailWord_3684404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684404).length < 2 ^ (prefixWord ++ tailWord_3684404).sum := by decide
  have hdescent : baseEnd_3684404 < baseStart_3684404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684415 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 7]
def baseStart_3684415 : Nat := 118140960795 + 3684415 * 2 ^ 59
def prefixEnd_3684415 : Nat := 4983230072969 + 3 ^ 40 * 3684415 * 2
def baseEnd_3684415 : Nat := 420416850141179431792931

theorem tailTrace_3684415 : CollatzResearch.WordTrace tailWord_3684415 prefixEnd_3684415 420416850141179431792931 := by
  unfold tailWord_3684415
  simp only [CollatzResearch.WordTrace]
  refine ⟨134381654947001177830118699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89587769964667451886745799 134381654947001177830118699)
  ·
    refine ⟨201572482420501766745178049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134381654947001177830118699 201572482420501766745178049)
    ·
      refine ⟨151179361815376325058883537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201572482420501766745178049 151179361815376325058883537)
      ·
        refine ⟨113384521361532243794162653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151179361815376325058883537 113384521361532243794162653)
        ·
          refine ⟨42519195510574591422810995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113384521361532243794162653 42519195510574591422810995)
          ·
            refine ⟨63778793265861887134216493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42519195510574591422810995 63778793265861887134216493)
            ·
              refine ⟨23917047474698207675331185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63778793265861887134216493 23917047474698207675331185)
              ·
                refine ⟨17937785606023655756498389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23917047474698207675331185 17937785606023655756498389)
                ·
                  refine ⟨420416850141179431792931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17937785606023655756498389 420416850141179431792931)
                  ·
                    rfl

theorem cell22_3684415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 7].length) (baseStart_3684415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684415 prefixEnd_3684415 := by exact prefixLift 3684415
  have htrace : WordTrace (prefixWord ++ tailWord_3684415) baseStart_3684415 baseEnd_3684415 := by
    simpa [prefixWord, tailWord_3684415, baseEnd_3684415] using wordTrace_append hprefix tailTrace_3684415
  have hstable : (prefixWord ++ tailWord_3684415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684415).length < 2 ^ (prefixWord ++ tailWord_3684415).sum := by decide
  have hdescent : baseEnd_3684415 < baseStart_3684415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684419 : List Nat := [1, 1, 1, 3, 1, 2, 2, 7, 1, 3]
def baseStart_3684419 : Nat := 118140960795 + 3684419 * 2 ^ 59
def prefixEnd_3684419 : Nat := 4983230072969 + 3 ^ 40 * 3684419 * 2
def baseEnd_3684419 : Nat := 1261251919705283618278781

theorem tailTrace_3684419 : CollatzResearch.WordTrace tailWord_3684419 prefixEnd_3684419 1261251919705283618278781 := by
  unfold tailWord_3684419
  simp only [CollatzResearch.WordTrace]
  refine ⟨134381800838986686513264311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89587867225991124342176207 134381800838986686513264311)
  ·
    refine ⟨201572701258480029769896467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134381800838986686513264311 201572701258480029769896467)
    ·
      refine ⟨302359051887720044654844701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201572701258480029769896467 302359051887720044654844701)
      ·
        refine ⟨113384644457895016745566763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302359051887720044654844701 113384644457895016745566763)
        ·
          refine ⟨170076966686842525118350145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113384644457895016745566763 170076966686842525118350145)
          ·
            refine ⟨127557725015131893838762609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170076966686842525118350145 127557725015131893838762609)
            ·
              refine ⟨95668293761348920379071957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127557725015131893838762609 95668293761348920379071957)
              ·
                refine ⟨2242225635031615321384499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95668293761348920379071957 2242225635031615321384499)
                ·
                  refine ⟨3363338452547422982076749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242225635031615321384499 3363338452547422982076749)
                  ·
                    refine ⟨1261251919705283618278781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3363338452547422982076749 1261251919705283618278781)
                    ·
                      rfl

theorem cell22_3684419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 1, 3].length) (baseStart_3684419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684419 prefixEnd_3684419 := by exact prefixLift 3684419
  have htrace : WordTrace (prefixWord ++ tailWord_3684419) baseStart_3684419 baseEnd_3684419 := by
    simpa [prefixWord, tailWord_3684419, baseEnd_3684419] using wordTrace_append hprefix tailTrace_3684419
  have hstable : (prefixWord ++ tailWord_3684419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684419).length < 2 ^ (prefixWord ++ tailWord_3684419).sum := by decide
  have hdescent : baseEnd_3684419 < baseStart_3684419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684509 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_3684509 : Nat := 118140960795 + 3684509 * 2 ^ 59
def prefixEnd_3684509 : Nat := 4983230072969 + 3 ^ 40 * 3684509 * 2
def baseEnd_3684509 : Nat := 1261282728544553383528505

theorem tailTrace_3684509 : CollatzResearch.WordTrace tailWord_3684509 prefixEnd_3684509 1261282728544553383528505 := by
  unfold tailWord_3684509
  simp only [CollatzResearch.WordTrace]
  refine ⟨134385083408660631884040581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89590055605773754589360387 134385083408660631884040581)
  ·
    refine ⟨25197203139123868478257609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134385083408660631884040581 25197203139123868478257609)
    ·
      refine ⟨18897902354342901358693207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25197203139123868478257609 18897902354342901358693207)
      ·
        refine ⟨28346853531514352038039811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18897902354342901358693207 28346853531514352038039811)
        ·
          refine ⟨42520280297271528057059717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28346853531514352038039811 42520280297271528057059717)
          ·
            refine ⟨7972552555738411510698697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42520280297271528057059717 7972552555738411510698697)
            ·
              refine ⟨5979414416803808633024023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7972552555738411510698697 5979414416803808633024023)
              ·
                refine ⟨8969121625205712949536035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5979414416803808633024023 8969121625205712949536035)
                ·
                  refine ⟨13453682437808569424304053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8969121625205712949536035 13453682437808569424304053)
                  ·
                    refine ⟨1261282728544553383528505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13453682437808569424304053 1261282728544553383528505)
                    ·
                      rfl

theorem cell22_3684509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_3684509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684509 prefixEnd_3684509 := by exact prefixLift 3684509
  have htrace : WordTrace (prefixWord ++ tailWord_3684509) baseStart_3684509 baseEnd_3684509 := by
    simpa [prefixWord, tailWord_3684509, baseEnd_3684509] using wordTrace_append hprefix tailTrace_3684509
  have hstable : (prefixWord ++ tailWord_3684509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684509).length < 2 ^ (prefixWord ++ tailWord_3684509).sum := by decide
  have hdescent : baseEnd_3684509 < baseStart_3684509 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684627 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 5, 5]
def baseStart_3684627 : Nat := 118140960795 + 3684627 * 2 ^ 59
def prefixEnd_3684627 : Nat := 4983230072969 + 3 ^ 40 * 3684627 * 2
def baseEnd_3684627 : Nat := 1261323122356040409078143

theorem tailTrace_3684627 : CollatzResearch.WordTrace tailWord_3684627 prefixEnd_3684627 1261323122356040409078143 := by
  unfold tailWord_3684627
  simp only [CollatzResearch.WordTrace]
  refine ⟨134389387222233138036836135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89592924814822092024557423 134389387222233138036836135)
  ·
    refine ⟨201584080833349707055254203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134389387222233138036836135 201584080833349707055254203)
    ·
      refine ⟨302376121250024560582881305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201584080833349707055254203 302376121250024560582881305)
      ·
        refine ⟨226782090937518420437160979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302376121250024560582881305 226782090937518420437160979)
        ·
          refine ⟨340173136406277630655741469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226782090937518420437160979 340173136406277630655741469)
          ·
            refine ⟨127564926152354111495903051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340173136406277630655741469 127564926152354111495903051)
            ·
              refine ⟨191347389228531167243854577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127564926152354111495903051 191347389228531167243854577)
              ·
                refine ⟨143510541921398375432890933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191347389228531167243854577 143510541921398375432890933)
                ·
                  refine ⟨13454113305131097696833525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 143510541921398375432890933 13454113305131097696833525)
                  ·
                    refine ⟨1261323122356040409078143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13454113305131097696833525 1261323122356040409078143)
                    ·
                      rfl

theorem cell22_3684627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 5].length) (baseStart_3684627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684627 prefixEnd_3684627 := by exact prefixLift 3684627
  have htrace : WordTrace (prefixWord ++ tailWord_3684627) baseStart_3684627 baseEnd_3684627 := by
    simpa [prefixWord, tailWord_3684627, baseEnd_3684627] using wordTrace_append hprefix tailTrace_3684627
  have hstable : (prefixWord ++ tailWord_3684627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684627).length < 2 ^ (prefixWord ++ tailWord_3684627).sum := by decide
  have hdescent : baseEnd_3684627 < baseStart_3684627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684631 : List Nat := [1, 1, 3, 4, 1, 2, 3, 2, 1, 4]
def baseStart_3684631 : Nat := 118140960795 + 3684631 * 2 ^ 59
def prefixEnd_3684631 : Nat := 4983230072969 + 3 ^ 40 * 3684631 * 2
def baseEnd_3684631 : Nat := 1261324491637785731978131

theorem tailTrace_3684631 : CollatzResearch.WordTrace tailWord_3684631 prefixEnd_3684631 1261324491637785731978131 := by
  unfold tailWord_3684631
  simp only [CollatzResearch.WordTrace]
  refine ⟨134389533114218646719981747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89593022076145764479987831 134389533114218646719981747)
  ·
    refine ⟨201584299671327970079972621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134389533114218646719981747 201584299671327970079972621)
    ·
      refine ⟨75594112376747988779989733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201584299671327970079972621 75594112376747988779989733)
      ·
        refine ⟨14173896070640247896248075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75594112376747988779989733 14173896070640247896248075)
        ·
          refine ⟨21260844105960371844372113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14173896070640247896248075 21260844105960371844372113)
          ·
            refine ⟨15945633079470278883279085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21260844105960371844372113 15945633079470278883279085)
            ·
              refine ⟨5979612404801354581229657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15945633079470278883279085 5979612404801354581229657)
              ·
                refine ⟨4484709303601015935922243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5979612404801354581229657 4484709303601015935922243)
                ·
                  refine ⟨6727063955401523903883365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4484709303601015935922243 6727063955401523903883365)
                  ·
                    refine ⟨1261324491637785731978131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6727063955401523903883365 1261324491637785731978131)
                    ·
                      rfl

theorem cell22_3684631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_3684631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684631 prefixEnd_3684631 := by exact prefixLift 3684631
  have htrace : WordTrace (prefixWord ++ tailWord_3684631) baseStart_3684631 baseEnd_3684631 := by
    simpa [prefixWord, tailWord_3684631, baseEnd_3684631] using wordTrace_append hprefix tailTrace_3684631
  have hstable : (prefixWord ++ tailWord_3684631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684631).length < 2 ^ (prefixWord ++ tailWord_3684631).sum := by decide
  have hdescent : baseEnd_3684631 < baseStart_3684631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684644 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 3, 5]
def baseStart_3684644 : Nat := 118140960795 + 3684644 * 2 ^ 59
def prefixEnd_3684644 : Nat := 4983230072969 + 3 ^ 40 * 3684644 * 2
def baseEnd_3684644 : Nat := 1261328941803458031403091

theorem tailTrace_3684644 : CollatzResearch.WordTrace tailWord_3684644 prefixEnd_3684644 1261328941803458031403091 := by
  unfold tailWord_3684644
  simp only [CollatzResearch.WordTrace]
  refine ⟨67195003631585774970102493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89593338175447699960136657 67195003631585774970102493)
  ·
    refine ⟨25198126361844665613788435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67195003631585774970102493 25198126361844665613788435)
    ·
      refine ⟨37797189542766998420682653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25198126361844665613788435 37797189542766998420682653)
      ·
        refine ⟨14173946078537624407755995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37797189542766998420682653 14173946078537624407755995)
        ·
          refine ⟨21260919117806436611633993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14173946078537624407755995 21260919117806436611633993)
          ·
            refine ⟨15945689338354827458725495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21260919117806436611633993 15945689338354827458725495)
            ·
              refine ⟨23918534007532241188088243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15945689338354827458725495 23918534007532241188088243)
              ·
                refine ⟨35877801011298361782132365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23918534007532241188088243 35877801011298361782132365)
                ·
                  refine ⟨13454175379236885668299637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35877801011298361782132365 13454175379236885668299637)
                  ·
                    refine ⟨1261328941803458031403091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13454175379236885668299637 1261328941803458031403091)
                    ·
                      rfl

theorem cell22_3684644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_3684644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684644 prefixEnd_3684644 := by exact prefixLift 3684644
  have htrace : WordTrace (prefixWord ++ tailWord_3684644) baseStart_3684644 baseEnd_3684644 := by
    simpa [prefixWord, tailWord_3684644, baseEnd_3684644] using wordTrace_append hprefix tailTrace_3684644
  have hstable : (prefixWord ++ tailWord_3684644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684644).length < 2 ^ (prefixWord ++ tailWord_3684644).sum := by decide
  have hdescent : baseEnd_3684644 < baseStart_3684644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684657 : List Nat := [1, 2, 2, 3, 14]
def baseStart_3684657 : Nat := 118140960795 + 3684657 * 2 ^ 59
def prefixEnd_3684657 : Nat := 4983230072969 + 3 ^ 40 * 3684657 * 2
def baseEnd_3684657 : Nat := 5190672394934692719457

theorem tailTrace_3684657 : CollatzResearch.WordTrace tailWord_3684657 prefixEnd_3684657 5190672394934692719457 := by
  unfold tailWord_3684657
  simp only [CollatzResearch.WordTrace]
  refine ⟨134390481412124453160428225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89593654274749635440285483 134390481412124453160428225)
  ·
    refine ⟨100792861059093339870321169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134390481412124453160428225 100792861059093339870321169)
    ·
      refine ⟨75594645794320004902740877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100792861059093339870321169 75594645794320004902740877)
      ·
        refine ⟨28347992172870001838527829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75594645794320004902740877 28347992172870001838527829)
        ·
          refine ⟨5190672394934692719457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 28347992172870001838527829 5190672394934692719457)
          ·
            rfl

theorem cell22_3684657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 14].length) (baseStart_3684657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684657 prefixEnd_3684657 := by exact prefixLift 3684657
  have htrace : WordTrace (prefixWord ++ tailWord_3684657) baseStart_3684657 baseEnd_3684657 := by
    simpa [prefixWord, tailWord_3684657, baseEnd_3684657] using wordTrace_append hprefix tailTrace_3684657
  have hstable : (prefixWord ++ tailWord_3684657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684657).length < 2 ^ (prefixWord ++ tailWord_3684657).sum := by decide
  have hdescent : baseEnd_3684657 < baseStart_3684657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684659 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 2, 4]
def baseStart_3684659 : Nat := 118140960795 + 3684659 * 2 ^ 59
def prefixEnd_3684659 : Nat := 4983230072969 + 3 ^ 40 * 3684659 * 2
def baseEnd_3684659 : Nat := 1261334076610002992278045

theorem tailTrace_3684659 : CollatzResearch.WordTrace tailWord_3684659 prefixEnd_3684659 1261334076610002992278045 := by
  unfold tailWord_3684659
  simp only [CollatzResearch.WordTrace]
  refine ⟨134390554358117207502001031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89593702905411471668000687 134390554358117207502001031)
  ·
    refine ⟨201585831537175811253001547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134390554358117207502001031 201585831537175811253001547)
    ·
      refine ⟨302378747305763716879502321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201585831537175811253001547 302378747305763716879502321)
      ·
        refine ⟨226784060479322787659626741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302378747305763716879502321 226784060479322787659626741)
        ·
          refine ⟨21261005669936511343090007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226784060479322787659626741 21261005669936511343090007)
          ·
            refine ⟨31891508504904767014635011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21261005669936511343090007 31891508504904767014635011)
            ·
              refine ⟨47837262757357150521952517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31891508504904767014635011 47837262757357150521952517)
              ·
                refine ⟨8969486767004465722866097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47837262757357150521952517 8969486767004465722866097)
                ·
                  refine ⟨6727115075253349292149573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8969486767004465722866097 6727115075253349292149573)
                  ·
                    refine ⟨1261334076610002992278045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6727115075253349292149573 1261334076610002992278045)
                    ·
                      rfl

theorem cell22_3684659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 4].length) (baseStart_3684659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684659 prefixEnd_3684659 := by exact prefixLift 3684659
  have htrace : WordTrace (prefixWord ++ tailWord_3684659) baseStart_3684659 baseEnd_3684659 := by
    simpa [prefixWord, tailWord_3684659, baseEnd_3684659] using wordTrace_append hprefix tailTrace_3684659
  have hstable : (prefixWord ++ tailWord_3684659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684659).length < 2 ^ (prefixWord ++ tailWord_3684659).sum := by decide
  have hdescent : baseEnd_3684659 < baseStart_3684659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684693 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 2, 4]
def baseStart_3684693 : Nat := 118140960795 + 3684693 * 2 ^ 59
def prefixEnd_3684693 : Nat := 4983230072969 + 3 ^ 40 * 3684693 * 2
def baseEnd_3684693 : Nat := 1261345715504838236927941

theorem tailTrace_3684693 : CollatzResearch.WordTrace tailWord_3684693 prefixEnd_3684693 1261345715504838236927941 := by
  unfold tailWord_3684693
  simp only [CollatzResearch.WordTrace]
  refine ⟨134391794439994031308738733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89594529626662687539159155 134391794439994031308738733)
  ·
    refine ⟨50396922914997761740777025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134391794439994031308738733 50396922914997761740777025)
    ·
      refine ⟨37797692186248321305582769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50396922914997761740777025 37797692186248321305582769)
      ·
        refine ⟨28348269139686240979187077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37797692186248321305582769 28348269139686240979187077)
        ·
          refine ⟨5315300463691170183597577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28348269139686240979187077 5315300463691170183597577)
          ·
            refine ⟨3986475347768377637698183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5315300463691170183597577 3986475347768377637698183)
            ·
              refine ⟨5979713021652566456547275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3986475347768377637698183 5979713021652566456547275)
              ·
                refine ⟨8969569532478849684820913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5979713021652566456547275 8969569532478849684820913)
                ·
                  refine ⟨6727177149359137263615685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8969569532478849684820913 6727177149359137263615685)
                  ·
                    refine ⟨1261345715504838236927941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6727177149359137263615685 1261345715504838236927941)
                    ·
                      rfl

theorem cell22_3684693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_3684693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684693 prefixEnd_3684693 := by exact prefixLift 3684693
  have htrace : WordTrace (prefixWord ++ tailWord_3684693) baseStart_3684693 baseEnd_3684693 := by
    simpa [prefixWord, tailWord_3684693, baseEnd_3684693] using wordTrace_append hprefix tailTrace_3684693
  have hstable : (prefixWord ++ tailWord_3684693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684693).length < 2 ^ (prefixWord ++ tailWord_3684693).sum := by decide
  have hdescent : baseEnd_3684693 < baseStart_3684693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684719 : List Nat := [1, 1, 2, 1, 3, 1, 2, 6, 5]
def baseStart_3684719 : Nat := 118140960795 + 3684719 * 2 ^ 59
def prefixEnd_3684719 : Nat := 4983230072969 + 3 ^ 40 * 3684719 * 2
def baseEnd_3684719 : Nat := 420451538612060945259287

theorem tailTrace_3684719 : CollatzResearch.WordTrace tailWord_3684719 prefixEnd_3684719 420451538612060945259287 := by
  unfold tailWord_3684719
  simp only [CollatzResearch.WordTrace]
  refine ⟨134392742737899837749185211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89595161825266558499456807 134392742737899837749185211)
  ·
    refine ⟨201589114106849756623777817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134392742737899837749185211 201589114106849756623777817)
    ·
      refine ⟨151191835580137317467833363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201589114106849756623777817 151191835580137317467833363)
      ·
        refine ⟨226787753370205976201750045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151191835580137317467833363 226787753370205976201750045)
        ·
          refine ⟨85045407513827241075656267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226787753370205976201750045 85045407513827241075656267)
          ·
            refine ⟨127568111270740861613484401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85045407513827241075656267 127568111270740861613484401)
            ·
              refine ⟨95676083453055646210113301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127568111270740861613484401 95676083453055646210113301)
              ·
                refine ⟨4484816411861983416099061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95676083453055646210113301 4484816411861983416099061)
                ·
                  refine ⟨420451538612060945259287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4484816411861983416099061 420451538612060945259287)
                  ·
                    rfl

theorem cell22_3684719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 5].length) (baseStart_3684719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684719 prefixEnd_3684719 := by exact prefixLift 3684719
  have htrace : WordTrace (prefixWord ++ tailWord_3684719) baseStart_3684719 baseEnd_3684719 := by
    simpa [prefixWord, tailWord_3684719, baseEnd_3684719] using wordTrace_append hprefix tailTrace_3684719
  have hstable : (prefixWord ++ tailWord_3684719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684719).length < 2 ^ (prefixWord ++ tailWord_3684719).sum := by decide
  have hdescent : baseEnd_3684719 < baseStart_3684719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684794 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 3, 6]
def baseStart_3684794 : Nat := 118140960795 + 3684794 * 2 ^ 59
def prefixEnd_3684794 : Nat := 4983230072969 + 3 ^ 40 * 3684794 * 2
def baseEnd_3684794 : Nat := 1261380289868907640152631

theorem tailTrace_3684794 : CollatzResearch.WordTrace tailWord_3684794 prefixEnd_3684794 1261380289868907640152631 := by
  unfold tailWord_3684794
  simp only [CollatzResearch.WordTrace]
  refine ⟨33598869553157031389541359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89596985475085417038776957 33598869553157031389541359)
  ·
    refine ⟨50398304329735547084312039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33598869553157031389541359 50398304329735547084312039)
    ·
      refine ⟨75597456494603320626468059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50398304329735547084312039 75597456494603320626468059)
      ·
        refine ⟨113396184741904980939702089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75597456494603320626468059 113396184741904980939702089)
        ·
          refine ⟨85047138556428735704776567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113396184741904980939702089 85047138556428735704776567)
          ·
            refine ⟨127570707834643103557164851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85047138556428735704776567 127570707834643103557164851)
            ·
              refine ⟨191356061751964655335747277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127570707834643103557164851 191356061751964655335747277)
              ·
                refine ⟨71758523156986745750905229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 191356061751964655335747277 71758523156986745750905229)
                ·
                  refine ⟨26909446183870029656589461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71758523156986745750905229 26909446183870029656589461)
                  ·
                    refine ⟨1261380289868907640152631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26909446183870029656589461 1261380289868907640152631)
                    ·
                      rfl

theorem cell22_3684794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_3684794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684794 prefixEnd_3684794 := by exact prefixLift 3684794
  have htrace : WordTrace (prefixWord ++ tailWord_3684794) baseStart_3684794 baseEnd_3684794 := by
    simpa [prefixWord, tailWord_3684794, baseEnd_3684794] using wordTrace_append hprefix tailTrace_3684794
  have hstable : (prefixWord ++ tailWord_3684794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684794).length < 2 ^ (prefixWord ++ tailWord_3684794).sum := by decide
  have hdescent : baseEnd_3684794 < baseStart_3684794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684809 : List Nat := [1, 2, 1, 1, 2, 1, 6, 8]
def baseStart_3684809 : Nat := 118140960795 + 3684809 * 2 ^ 59
def prefixEnd_3684809 : Nat := 4983230072969 + 3 ^ 40 * 3684809 * 2
def baseEnd_3684809 : Nat := 140153936075050289003065

theorem tailTrace_3684809 : CollatzResearch.WordTrace tailWord_3684809 prefixEnd_3684809 140153936075050289003065 := by
  unfold tailWord_3684809
  simp only [CollatzResearch.WordTrace]
  refine ⟨134396025307573783119961481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89597350205049188746640987 134396025307573783119961481)
  ·
    refine ⟨100797018980680337339971111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134396025307573783119961481 100797018980680337339971111)
    ·
      refine ⟨151195528471020506009956667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100797018980680337339971111 151195528471020506009956667)
      ·
        refine ⟨226793292706530759014935001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151195528471020506009956667 226793292706530759014935001)
        ·
          refine ⟨170094969529898069261201251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226793292706530759014935001 170094969529898069261201251)
          ·
            refine ⟨255142454294847103891801877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170094969529898069261201251 255142454294847103891801877)
            ·
              refine ⟨11959802545070957994928213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 255142454294847103891801877 11959802545070957994928213)
              ·
                refine ⟨140153936075050289003065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11959802545070957994928213 140153936075050289003065)
                ·
                  rfl

theorem cell22_3684809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 8].length) (baseStart_3684809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684809 prefixEnd_3684809 := by exact prefixLift 3684809
  have htrace : WordTrace (prefixWord ++ tailWord_3684809) baseStart_3684809 baseEnd_3684809 := by
    simpa [prefixWord, tailWord_3684809, baseEnd_3684809] using wordTrace_append hprefix tailTrace_3684809
  have hstable : (prefixWord ++ tailWord_3684809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684809).length < 2 ^ (prefixWord ++ tailWord_3684809).sum := by decide
  have hdescent : baseEnd_3684809 < baseStart_3684809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684875 : List Nat := [1, 1, 1, 1, 7, 1, 1, 5, 1, 3]
def baseStart_3684875 : Nat := 118140960795 + 3684875 * 2 ^ 59
def prefixEnd_3684875 : Nat := 4983230072969 + 3 ^ 40 * 3684875 * 2
def baseEnd_3684875 : Nat := 1261408017824250428877383

theorem tailTrace_3684875 : CollatzResearch.WordTrace tailWord_3684875 prefixEnd_3684875 1261408017824250428877383 := by
  unfold tailWord_3684875
  simp only [CollatzResearch.WordTrace]
  refine ⟨134398432525334676391864079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89598955016889784261242719 134398432525334676391864079)
  ·
    refine ⟨201597648788002014587796119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134398432525334676391864079 201597648788002014587796119)
    ·
      refine ⟨302396473182003021881694179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201597648788002014587796119 302396473182003021881694179)
      ·
        refine ⟨453594709773004532822541269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302396473182003021881694179 453594709773004532822541269)
        ·
          refine ⟨10631126010304793738028311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 453594709773004532822541269 10631126010304793738028311)
          ·
            refine ⟨15946689015457190607042467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10631126010304793738028311 15946689015457190607042467)
            ·
              refine ⟨23920033523185785910563701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15946689015457190607042467 23920033523185785910563701)
              ·
                refine ⟨2242503142798667429115347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23920033523185785910563701 2242503142798667429115347)
                ·
                  refine ⟨3363754714198001143673021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242503142798667429115347 3363754714198001143673021)
                  ·
                    refine ⟨1261408017824250428877383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3363754714198001143673021 1261408017824250428877383)
                    ·
                      rfl

theorem cell22_3684875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 1, 3].length) (baseStart_3684875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684875 prefixEnd_3684875 := by exact prefixLift 3684875
  have htrace : WordTrace (prefixWord ++ tailWord_3684875) baseStart_3684875 baseEnd_3684875 := by
    simpa [prefixWord, tailWord_3684875, baseEnd_3684875] using wordTrace_append hprefix tailTrace_3684875
  have hstable : (prefixWord ++ tailWord_3684875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684875).length < 2 ^ (prefixWord ++ tailWord_3684875).sum := by decide
  have hdescent : baseEnd_3684875 < baseStart_3684875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684888 : List Nat := [2, 1, 2, 3, 3, 1, 3, 2, 5]
def baseStart_3684888 : Nat := 118140960795 + 3684888 * 2 ^ 59
def prefixEnd_3684888 : Nat := 4983230072969 + 3 ^ 40 * 3684888 * 2
def baseEnd_3684888 : Nat := 420470822663307576100781

theorem tailTrace_3684888 : CollatzResearch.WordTrace tailWord_3684888 prefixEnd_3684888 420470822663307576100781 := by
  unfold tailWord_3684888
  simp only [CollatzResearch.WordTrace]
  refine ⟨67199453337143789806043659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89599271116191719741391545 67199453337143789806043659)
  ·
    refine ⟨100799180005715684709065489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67199453337143789806043659 100799180005715684709065489)
    ·
      refine ⟨75599385004286763531799117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100799180005715684709065489 75599385004286763531799117)
      ·
        refine ⟨28349769376607536324424669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75599385004286763531799117 28349769376607536324424669)
        ·
          refine ⟨10631163516227826121659251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28349769376607536324424669 10631163516227826121659251)
          ·
            refine ⟨15946745274341739182488877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10631163516227826121659251 15946745274341739182488877)
            ·
              refine ⟨5980029477878152193433329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15946745274341739182488877 5980029477878152193433329)
              ·
                refine ⟨4485022108408614145074997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5980029477878152193433329 4485022108408614145074997)
                ·
                  refine ⟨420470822663307576100781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4485022108408614145074997 420470822663307576100781)
                  ·
                    rfl

theorem cell22_3684888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2, 5].length) (baseStart_3684888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684888 prefixEnd_3684888 := by exact prefixLift 3684888
  have htrace : WordTrace (prefixWord ++ tailWord_3684888) baseStart_3684888 baseEnd_3684888 := by
    simpa [prefixWord, tailWord_3684888, baseEnd_3684888] using wordTrace_append hprefix tailTrace_3684888
  have hstable : (prefixWord ++ tailWord_3684888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684888).length < 2 ^ (prefixWord ++ tailWord_3684888).sum := by decide
  have hdescent : baseEnd_3684888 < baseStart_3684888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684901 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 5, 4]
def baseStart_3684901 : Nat := 118140960795 + 3684901 * 2 ^ 59
def prefixEnd_3684901 : Nat := 4983230072969 + 3 ^ 40 * 3684901 * 2
def baseEnd_3684901 : Nat := 1261416918155595027727303

theorem tailTrace_3684901 : CollatzResearch.WordTrace tailWord_3684901 prefixEnd_3684901 1261416918155595027727303 := by
  unfold tailWord_3684901
  simp only [CollatzResearch.WordTrace]
  refine ⟨134399380823240482832310557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89599587215493655221540371 134399380823240482832310557)
  ·
    refine ⟨50399767808715181062116459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134399380823240482832310557 50399767808715181062116459)
    ·
      refine ⟨75599651713072771593174689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50399767808715181062116459 75599651713072771593174689)
      ·
        refine ⟨56699738784804578694881017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75599651713072771593174689 56699738784804578694881017)
        ·
          refine ⟨42524804088603434021160763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56699738784804578694881017 42524804088603434021160763)
          ·
            refine ⟨63787206132905151031741145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42524804088603434021160763 63787206132905151031741145)
            ·
              refine ⟨47840404599678863273805859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63787206132905151031741145 47840404599678863273805859)
              ·
                refine ⟨71760606899518294910708789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47840404599678863273805859 71760606899518294910708789)
                ·
                  refine ⟨6727556896829840147878949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71760606899518294910708789 6727556896829840147878949)
                  ·
                    refine ⟨1261416918155595027727303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6727556896829840147878949 1261416918155595027727303)
                    ·
                      rfl

theorem cell22_3684901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_3684901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684901 prefixEnd_3684901 := by exact prefixLift 3684901
  have htrace : WordTrace (prefixWord ++ tailWord_3684901) baseStart_3684901 baseEnd_3684901 := by
    simpa [prefixWord, tailWord_3684901, baseEnd_3684901] using wordTrace_append hprefix tailTrace_3684901
  have hstable : (prefixWord ++ tailWord_3684901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684901).length < 2 ^ (prefixWord ++ tailWord_3684901).sum := by decide
  have hdescent : baseEnd_3684901 < baseStart_3684901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684926 : List Nat := [4, 2, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_3684926 : Nat := 118140960795 + 3684926 * 2 ^ 59
def prefixEnd_3684926 : Nat := 4983230072969 + 3 ^ 40 * 3684926 * 2
def baseEnd_3684926 : Nat := 1261425476166503295852227

theorem tailTrace_3684926 : CollatzResearch.WordTrace tailWord_3684926 prefixEnd_3684926 1261425476166503295852227 := by
  unfold tailWord_3684926
  simp only [CollatzResearch.WordTrace]
  refine ⟨16800036581018739012746329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89600195098766608067980421 16800036581018739012746329)
  ·
    refine ⟨12600027435764054259559747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16800036581018739012746329 12600027435764054259559747)
    ·
      refine ⟨18900041153646081389339621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12600027435764054259559747 18900041153646081389339621)
      ·
        refine ⟨3543757716308640260501179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18900041153646081389339621 3543757716308640260501179)
        ·
          refine ⟨5315636574462960390751769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3543757716308640260501179 5315636574462960390751769)
          ·
            refine ⟨3986727430847220293063827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5315636574462960390751769 3986727430847220293063827)
            ·
              refine ⟨5980091146270830439595741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3986727430847220293063827 5980091146270830439595741)
              ·
                refine ⟨2242534179851561414848403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5980091146270830439595741 2242534179851561414848403)
                ·
                  refine ⟨3363801269777342122272605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242534179851561414848403 3363801269777342122272605)
                  ·
                    refine ⟨1261425476166503295852227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3363801269777342122272605 1261425476166503295852227)
                    ·
                      rfl

theorem cell22_3684926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_3684926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684926 prefixEnd_3684926 := by exact prefixLift 3684926
  have htrace : WordTrace (prefixWord ++ tailWord_3684926) baseStart_3684926 baseEnd_3684926 := by
    simpa [prefixWord, tailWord_3684926, baseEnd_3684926] using wordTrace_append hprefix tailTrace_3684926
  have hstable : (prefixWord ++ tailWord_3684926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684926).length < 2 ^ (prefixWord ++ tailWord_3684926).sum := by decide
  have hdescent : baseEnd_3684926 < baseStart_3684926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684931 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 1, 5]
def baseStart_3684931 : Nat := 118140960795 + 3684931 * 2 ^ 59
def prefixEnd_3684931 : Nat := 4983230072969 + 3 ^ 40 * 3684931 * 2
def baseEnd_3684931 : Nat := 1261427187768684949477211

theorem tailTrace_3684931 : CollatzResearch.WordTrace tailWord_3684931 prefixEnd_3684931 1261427187768684949477211 := by
  unfold tailWord_3684931
  simp only [CollatzResearch.WordTrace]
  refine ⟨134400475013131797955902647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89600316675421198637268431 134400475013131797955902647)
  ·
    refine ⟨201600712519697696933853971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134400475013131797955902647 201600712519697696933853971)
    ·
      refine ⟨302401068779546545400780957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201600712519697696933853971 302401068779546545400780957)
      ·
        refine ⟨113400400792329954525292859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302401068779546545400780957 113400400792329954525292859)
        ·
          refine ⟨170100601188494931787939289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113400400792329954525292859 170100601188494931787939289)
          ·
            refine ⟨127575450891371198840954467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170100601188494931787939289 127575450891371198840954467)
            ·
              refine ⟨191363176337056798261431701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127575450891371198840954467 191363176337056798261431701)
              ·
                refine ⟨8970148890799537418504611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 191363176337056798261431701 8970148890799537418504611)
                ·
                  refine ⟨13455223336199306127756917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8970148890799537418504611 13455223336199306127756917)
                  ·
                    refine ⟨1261427187768684949477211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13455223336199306127756917 1261427187768684949477211)
                    ·
                      rfl

theorem cell22_3684931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 5].length) (baseStart_3684931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684931 prefixEnd_3684931 := by exact prefixLift 3684931
  have htrace : WordTrace (prefixWord ++ tailWord_3684931) baseStart_3684931 baseEnd_3684931 := by
    simpa [prefixWord, tailWord_3684931, baseEnd_3684931] using wordTrace_append hprefix tailTrace_3684931
  have hstable : (prefixWord ++ tailWord_3684931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684931).length < 2 ^ (prefixWord ++ tailWord_3684931).sum := by decide
  have hdescent : baseEnd_3684931 < baseStart_3684931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3684961 : List Nat := [1, 2, 3, 1, 1, 4, 1, 9]
def baseStart_3684961 : Nat := 118140960795 + 3684961 * 2 ^ 59
def prefixEnd_3684961 : Nat := 4983230072969 + 3 ^ 40 * 3684961 * 2
def baseEnd_3684961 : Nat := 140159717486863874580791

theorem tailTrace_3684961 : CollatzResearch.WordTrace tailWord_3684961 prefixEnd_3684961 140159717486863874580791 := by
  unfold tailWord_3684961
  simp only [CollatzResearch.WordTrace]
  refine ⟨134401569203023113079494737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89601046135348742052996491 134401569203023113079494737)
  ·
    refine ⟨100801176902267334809621053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134401569203023113079494737 100801176902267334809621053)
    ·
      refine ⟨37800441338350250553607895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100801176902267334809621053 37800441338350250553607895)
      ·
        refine ⟨56700662007525375830411843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37800441338350250553607895 56700662007525375830411843)
        ·
          refine ⟨85050993011288063745617765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56700662007525375830411843 85050993011288063745617765)
          ·
            refine ⟨15947061189616511952303331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85050993011288063745617765 15947061189616511952303331)
            ·
              refine ⟨23920591784424767928454997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15947061189616511952303331 23920591784424767928454997)
              ·
                refine ⟨140159717486863874580791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23920591784424767928454997 140159717486863874580791)
                ·
                  rfl

theorem cell22_3684961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 9].length) (baseStart_3684961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3684961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3684961 prefixEnd_3684961 := by exact prefixLift 3684961
  have htrace : WordTrace (prefixWord ++ tailWord_3684961) baseStart_3684961 baseEnd_3684961 := by
    simpa [prefixWord, tailWord_3684961, baseEnd_3684961] using wordTrace_append hprefix tailTrace_3684961
  have hstable : (prefixWord ++ tailWord_3684961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3684961).length < 2 ^ (prefixWord ++ tailWord_3684961).sum := by decide
  have hdescent : baseEnd_3684961 < baseStart_3684961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3684961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685057 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 7]
def baseStart_3685057 : Nat := 118140960795 + 3685057 * 2 ^ 59
def prefixEnd_3685057 : Nat := 4983230072969 + 3 ^ 40 * 3685057 * 2
def baseEnd_3685057 : Nat := 420490106714554206942275

theorem tailTrace_3685057 : CollatzResearch.WordTrace tailWord_3685057 prefixEnd_3685057 420490106714554206942275 := by
  unfold tailWord_3685057
  simp only [CollatzResearch.WordTrace]
  refine ⟨134405070610675321474989425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89603380407116880983326283 134405070610675321474989425)
  ·
    refine ⟨100803802958006491106242069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134405070610675321474989425 100803802958006491106242069)
    ·
      refine ⟨4725178263656554270605097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100803802958006491106242069 4725178263656554270605097)
      ·
        refine ⟨3543883697742415702953823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4725178263656554270605097 3543883697742415702953823)
        ·
          refine ⟨5315825546613623554430735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3543883697742415702953823 5315825546613623554430735)
          ·
            refine ⟨7973738319920435331646103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5315825546613623554430735 7973738319920435331646103)
            ·
              refine ⟨11960607479880652997469155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7973738319920435331646103 11960607479880652997469155)
              ·
                refine ⟨17940911219820979496203733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11960607479880652997469155 17940911219820979496203733)
                ·
                  refine ⟨420490106714554206942275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17940911219820979496203733 420490106714554206942275)
                  ·
                    rfl

theorem cell22_3685057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 7].length) (baseStart_3685057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685057 prefixEnd_3685057 := by exact prefixLift 3685057
  have htrace : WordTrace (prefixWord ++ tailWord_3685057) baseStart_3685057 baseEnd_3685057 := by
    simpa [prefixWord, tailWord_3685057, baseEnd_3685057] using wordTrace_append hprefix tailTrace_3685057
  have hstable : (prefixWord ++ tailWord_3685057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685057).length < 2 ^ (prefixWord ++ tailWord_3685057).sum := by decide
  have hdescent : baseEnd_3685057 < baseStart_3685057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685102 : List Nat := [4, 1, 2, 1, 1, 3, 3, 3, 4]
def baseStart_3685102 : Nat := 118140960795 + 3685102 * 2 ^ 59
def prefixEnd_3685102 : Nat := 4983230072969 + 3 ^ 40 * 3685102 * 2
def baseEnd_3685102 : Nat := 420495241521099167817229

theorem tailTrace_3685102 : CollatzResearch.WordTrace tailWord_3685102 prefixEnd_3685102 420495241521099167817229 := by
  unfold tailWord_3685102
  simp only [CollatzResearch.WordTrace]
  refine ⟨16800838986939036770047195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89604474597008196106918373 16800838986939036770047195)
  ·
    refine ⟨25201258480408555155070793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16800838986939036770047195 25201258480408555155070793)
    ·
      refine ⟨18900943860306416366303095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25201258480408555155070793 18900943860306416366303095)
      ·
        refine ⟨28351415790459624549454643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18900943860306416366303095 28351415790459624549454643)
        ·
          refine ⟨42527123685689436824181965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28351415790459624549454643 42527123685689436824181965)
          ·
            refine ⟨15947671382133538809068237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42527123685689436824181965 15947671382133538809068237)
            ·
              refine ⟨5980376768300077053400589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15947671382133538809068237 5980376768300077053400589)
              ·
                refine ⟨2242641288112528895025221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5980376768300077053400589 2242641288112528895025221)
                ·
                  refine ⟨420495241521099167817229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2242641288112528895025221 420495241521099167817229)
                  ·
                    rfl

theorem cell22_3685102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 3, 4].length) (baseStart_3685102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685102 prefixEnd_3685102 := by exact prefixLift 3685102
  have htrace : WordTrace (prefixWord ++ tailWord_3685102) baseStart_3685102 baseEnd_3685102 := by
    simpa [prefixWord, tailWord_3685102, baseEnd_3685102] using wordTrace_append hprefix tailTrace_3685102
  have hstable : (prefixWord ++ tailWord_3685102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685102).length < 2 ^ (prefixWord ++ tailWord_3685102).sum := by decide
  have hdescent : baseEnd_3685102 < baseStart_3685102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685149 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 2, 4]
def baseStart_3685149 : Nat := 118140960795 + 3685149 * 2 ^ 59
def prefixEnd_3685149 : Nat := 4983230072969 + 3 ^ 40 * 3685149 * 2
def baseEnd_3685149 : Nat := 1261501813623805047526543

theorem tailTrace_3685149 : CollatzResearch.WordTrace tailWord_3685149 prefixEnd_3685149 1261501813623805047526543 := by
  unfold tailWord_3685149
  simp only [CollatzResearch.WordTrace]
  refine ⟨134408426126342021187338501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89605617417561347458225667 134408426126342021187338501)
  ·
    refine ⟨25201579898689128972625969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134408426126342021187338501 25201579898689128972625969)
    ·
      refine ⟨18901184924016846729469477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25201579898689128972625969 18901184924016846729469477)
      ·
        refine ⟨3543972173253158761775527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18901184924016846729469477 3543972173253158761775527)
        ·
          refine ⟨5315958259879738142663291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3543972173253158761775527 5315958259879738142663291)
          ·
            refine ⟨7973937389819607213994937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5315958259879738142663291 7973937389819607213994937)
            ·
              refine ⟨5980453042364705410496203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7973937389819607213994937 5980453042364705410496203)
              ·
                refine ⟨8970679563547058115744305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5980453042364705410496203 8970679563547058115744305)
                ·
                  refine ⟨6728009672660293586808229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8970679563547058115744305 6728009672660293586808229)
                  ·
                    refine ⟨1261501813623805047526543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6728009672660293586808229 1261501813623805047526543)
                    ·
                      rfl

theorem cell22_3685149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_3685149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685149 prefixEnd_3685149 := by exact prefixLift 3685149
  have htrace : WordTrace (prefixWord ++ tailWord_3685149) baseStart_3685149 baseEnd_3685149 := by
    simpa [prefixWord, tailWord_3685149, baseEnd_3685149] using wordTrace_append hprefix tailTrace_3685149
  have hstable : (prefixWord ++ tailWord_3685149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685149).length < 2 ^ (prefixWord ++ tailWord_3685149).sum := by decide
  have hdescent : baseEnd_3685149 < baseStart_3685149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685175 : List Nat := [1, 1, 3, 1, 2, 1, 6, 2, 5]
def baseStart_3685175 : Nat := 118140960795 + 3685175 * 2 ^ 59
def prefixEnd_3685175 : Nat := 4983230072969 + 3 ^ 40 * 3685175 * 2
def baseEnd_3685175 : Nat := 420503571318383215458821

theorem tailTrace_3685175 : CollatzResearch.WordTrace tailWord_3685175 prefixEnd_3685175 420503571318383215458821 := by
  unfold tailWord_3685175
  simp only [CollatzResearch.WordTrace]
  refine ⟨134409374424247827627784979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89606249616165218418523319 134409374424247827627784979)
  ·
    refine ⟨201614061636371741441677469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134409374424247827627784979 201614061636371741441677469)
    ·
      refine ⟨75605273113639403040629051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201614061636371741441677469 75605273113639403040629051)
      ·
        refine ⟨113407909670459104560943577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75605273113639403040629051 113407909670459104560943577)
        ·
          refine ⟨85055932252844328420707683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113407909670459104560943577 85055932252844328420707683)
          ·
            refine ⟨127583898379266492631061525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85055932252844328420707683 127583898379266492631061525)
            ·
              refine ⟨5980495236528116842081009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127583898379266492631061525 5980495236528116842081009)
              ·
                refine ⟨4485371427396087631560757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5980495236528116842081009 4485371427396087631560757)
                ·
                  refine ⟨420503571318383215458821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4485371427396087631560757 420503571318383215458821)
                  ·
                    rfl

theorem cell22_3685175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 2, 5].length) (baseStart_3685175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685175 prefixEnd_3685175 := by exact prefixLift 3685175
  have htrace : WordTrace (prefixWord ++ tailWord_3685175) baseStart_3685175 baseEnd_3685175 := by
    simpa [prefixWord, tailWord_3685175, baseEnd_3685175] using wordTrace_append hprefix tailTrace_3685175
  have hstable : (prefixWord ++ tailWord_3685175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685175).length < 2 ^ (prefixWord ++ tailWord_3685175).sum := by decide
  have hdescent : baseEnd_3685175 < baseStart_3685175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685205 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 3, 4]
def baseStart_3685205 : Nat := 118140960795 + 3685205 * 2 ^ 59
def prefixEnd_3685205 : Nat := 4983230072969 + 3 ^ 40 * 3685205 * 2
def baseEnd_3685205 : Nat := 1261520983568239568126371

theorem tailTrace_3685205 : CollatzResearch.WordTrace tailWord_3685205 prefixEnd_3685205 1261520983568239568126371 := by
  unfold tailWord_3685205
  simp only [CollatzResearch.WordTrace]
  refine ⟨134410468614139142751377069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89606979076092761834251379 134410468614139142751377069)
  ·
    refine ⟨50403925730302178531766401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134410468614139142751377069 50403925730302178531766401)
    ·
      refine ⟨37802944297726633898824801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50403925730302178531766401 37802944297726633898824801)
      ·
        refine ⟨28352208223294975424118601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37802944297726633898824801 28352208223294975424118601)
        ·
          refine ⟨21264156167471231568088951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28352208223294975424118601 21264156167471231568088951)
          ·
            refine ⟨31896234251206847352133427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21264156167471231568088951 31896234251206847352133427)
            ·
              refine ⟨47844351376810271028200141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31896234251206847352133427 47844351376810271028200141)
              ·
                refine ⟨17941631766303851635575053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47844351376810271028200141 17941631766303851635575053)
                ·
                  refine ⟨6728111912363944363340645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17941631766303851635575053 6728111912363944363340645)
                  ·
                    refine ⟨1261520983568239568126371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6728111912363944363340645 1261520983568239568126371)
                    ·
                      rfl

theorem cell22_3685205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_3685205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685205 prefixEnd_3685205 := by exact prefixLift 3685205
  have htrace : WordTrace (prefixWord ++ tailWord_3685205) baseStart_3685205 baseEnd_3685205 := by
    simpa [prefixWord, tailWord_3685205, baseEnd_3685205] using wordTrace_append hprefix tailTrace_3685205
  have hstable : (prefixWord ++ tailWord_3685205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685205).length < 2 ^ (prefixWord ++ tailWord_3685205).sum := by decide
  have hdescent : baseEnd_3685205 < baseStart_3685205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685237 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 6]
def baseStart_3685237 : Nat := 118140960795 + 3685237 * 2 ^ 59
def prefixEnd_3685237 : Nat := 4983230072969 + 3 ^ 40 * 3685237 * 2
def baseEnd_3685237 : Nat := 420510645940734050442091

theorem tailTrace_3685237 : CollatzResearch.WordTrace tailWord_3685237 prefixEnd_3685237 420510645940734050442091 := by
  unfold tailWord_3685237
  simp only [CollatzResearch.WordTrace]
  refine ⟨134411635750023212216541965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89607757166682141477694643 134411635750023212216541965)
  ·
    refine ⟨50404363406258704581203237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134411635750023212216541965 50404363406258704581203237)
    ·
      refine ⟨9450818138673507108975607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50404363406258704581203237 9450818138673507108975607)
      ·
        refine ⟨14176227208010260663463411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9450818138673507108975607 14176227208010260663463411)
        ·
          refine ⟨21264340812015390995195117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14176227208010260663463411 21264340812015390995195117)
          ·
            refine ⟨7974127804505771623198169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21264340812015390995195117 7974127804505771623198169)
            ·
              refine ⟨5980595853379328717398627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7974127804505771623198169 5980595853379328717398627)
              ·
                refine ⟨8970893780068993076097941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5980595853379328717398627 8970893780068993076097941)
                ·
                  refine ⟨420510645940734050442091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8970893780068993076097941 420510645940734050442091)
                  ·
                    rfl

theorem cell22_3685237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 6].length) (baseStart_3685237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685237 prefixEnd_3685237 := by exact prefixLift 3685237
  have htrace : WordTrace (prefixWord ++ tailWord_3685237) baseStart_3685237 baseEnd_3685237 := by
    simpa [prefixWord, tailWord_3685237, baseEnd_3685237] using wordTrace_append hprefix tailTrace_3685237
  have hstable : (prefixWord ++ tailWord_3685237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685237).length < 2 ^ (prefixWord ++ tailWord_3685237).sum := by decide
  have hdescent : baseEnd_3685237 < baseStart_3685237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685282 : List Nat := [3, 3, 1, 2, 2, 3, 8]
def baseStart_3685282 : Nat := 118140960795 + 3685282 * 2 ^ 59
def prefixEnd_3685282 : Nat := 4983230072969 + 3 ^ 40 * 3685282 * 2
def baseEnd_3685282 : Nat := 46723975638586556813005

theorem tailTrace_3685282 : CollatzResearch.WordTrace tailWord_3685282 prefixEnd_3685282 46723975638586556813005 := by
  unfold tailWord_3685282
  simp only [CollatzResearch.WordTrace]
  refine ⟨33603319258715046225482525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89608851356573456601286733 33603319258715046225482525)
  ·
    refine ⟨12601244722018142334555947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33603319258715046225482525 12601244722018142334555947)
    ·
      refine ⟨18901867083027213501833921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12601244722018142334555947 18901867083027213501833921)
      ·
        refine ⟨14176400312270410126375441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18901867083027213501833921 14176400312270410126375441)
        ·
          refine ⟨10632300234202807594781581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14176400312270410126375441 10632300234202807594781581)
          ·
            refine ⟨3987112587826052848043093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10632300234202807594781581 3987112587826052848043093)
            ·
              refine ⟨46723975638586556813005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3987112587826052848043093 46723975638586556813005)
              ·
                rfl

theorem cell22_3685282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 8].length) (baseStart_3685282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685282 prefixEnd_3685282 := by exact prefixLift 3685282
  have htrace : WordTrace (prefixWord ++ tailWord_3685282) baseStart_3685282 baseEnd_3685282 := by
    simpa [prefixWord, tailWord_3685282, baseEnd_3685282] using wordTrace_append hprefix tailTrace_3685282
  have hstable : (prefixWord ++ tailWord_3685282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685282).length < 2 ^ (prefixWord ++ tailWord_3685282).sum := by decide
  have hdescent : baseEnd_3685282 < baseStart_3685282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685372 : List Nat := [2, 2, 2, 1, 2, 4, 1, 2, 6]
def baseStart_3685372 : Nat := 118140960795 + 3685372 * 2 ^ 59
def prefixEnd_3685372 : Nat := 4983230072969 + 3 ^ 40 * 3685372 * 2
def baseEnd_3685372 : Nat := 420526050360368933066953

theorem tailTrace_3685372 : CollatzResearch.WordTrace tailWord_3685372 prefixEnd_3685372 420526050360368933066953 := by
  unfold tailWord_3685372
  simp only [CollatzResearch.WordTrace]
  refine ⟨67208279802267065136353185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89611039736356086848470913 67208279802267065136353185)
  ·
    refine ⟨50406209851700298852264889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67208279802267065136353185 50406209851700298852264889)
    ·
      refine ⟨37804657388775224139198667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50406209851700298852264889 37804657388775224139198667)
      ·
        refine ⟨56706986083162836208798001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37804657388775224139198667 56706986083162836208798001)
        ·
          refine ⟨42530239562372127156598501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56706986083162836208798001 42530239562372127156598501)
          ·
            refine ⟨7974419917944773841862219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42530239562372127156598501 7974419917944773841862219)
            ·
              refine ⟨11961629876917160762793329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7974419917944773841862219 11961629876917160762793329)
              ·
                refine ⟨8971222407687870572094997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11961629876917160762793329 8971222407687870572094997)
                ·
                  refine ⟨420526050360368933066953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8971222407687870572094997 420526050360368933066953)
                  ·
                    rfl

theorem cell22_3685372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 2, 6].length) (baseStart_3685372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685372 prefixEnd_3685372 := by exact prefixLift 3685372
  have htrace : WordTrace (prefixWord ++ tailWord_3685372) baseStart_3685372 baseEnd_3685372 := by
    simpa [prefixWord, tailWord_3685372, baseEnd_3685372] using wordTrace_append hprefix tailTrace_3685372
  have hstable : (prefixWord ++ tailWord_3685372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685372).length < 2 ^ (prefixWord ++ tailWord_3685372).sum := by decide
  have hdescent : baseEnd_3685372 < baseStart_3685372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685387 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 1, 5]
def baseStart_3685387 : Nat := 118140960795 + 3685387 * 2 ^ 59
def prefixEnd_3685387 : Nat := 4983230072969 + 3 ^ 40 * 3685387 * 2
def baseEnd_3685387 : Nat := 1261583285887651760075813

theorem tailTrace_3685387 : CollatzResearch.WordTrace tailWord_3685387 prefixEnd_3685387 1261583285887651760075813 := by
  unfold tailWord_3685387
  simp only [CollatzResearch.WordTrace]
  refine ⟨134417106699479787834502415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89611404466319858556334943 134417106699479787834502415)
  ·
    refine ⟨201625660049219681751753623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134417106699479787834502415 201625660049219681751753623)
    ·
      refine ⟨302438490073829522627630435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201625660049219681751753623 302438490073829522627630435)
      ·
        refine ⟨453657735110744283941445653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302438490073829522627630435 453657735110744283941445653)
        ·
          refine ⟨21265206333316138309755265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 453657735110744283941445653 21265206333316138309755265)
          ·
            refine ⟨15948904749987103732316449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21265206333316138309755265 15948904749987103732316449)
            ·
              refine ⟨11961678562490327799237337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15948904749987103732316449 11961678562490327799237337)
              ·
                refine ⟨8971258921867745849428003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11961678562490327799237337 8971258921867745849428003)
                ·
                  refine ⟨13456888382801618774142005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8971258921867745849428003 13456888382801618774142005)
                  ·
                    refine ⟨1261583285887651760075813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13456888382801618774142005 1261583285887651760075813)
                    ·
                      rfl

theorem cell22_3685387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 5].length) (baseStart_3685387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685387 prefixEnd_3685387 := by exact prefixLift 3685387
  have htrace : WordTrace (prefixWord ++ tailWord_3685387) baseStart_3685387 baseEnd_3685387 := by
    simpa [prefixWord, tailWord_3685387, baseEnd_3685387] using wordTrace_append hprefix tailTrace_3685387
  have hstable : (prefixWord ++ tailWord_3685387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685387).length < 2 ^ (prefixWord ++ tailWord_3685387).sum := by decide
  have hdescent : baseEnd_3685387 < baseStart_3685387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685402 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 4, 4]
def baseStart_3685402 : Nat := 118140960795 + 3685402 * 2 ^ 59
def prefixEnd_3685402 : Nat := 4983230072969 + 3 ^ 40 * 3685402 * 2
def baseEnd_3685402 : Nat := 1261588420694196720950767

theorem tailTrace_3685402 : CollatzResearch.WordTrace tailWord_3685402 prefixEnd_3685402 1261588420694196720950767 := by
  unfold tailWord_3685402
  simp only [CollatzResearch.WordTrace]
  refine ⟨33604413448606361349074615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89611769196283630264198973 33604413448606361349074615)
  ·
    refine ⟨50406620172909542023611923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33604413448606361349074615 50406620172909542023611923)
    ·
      refine ⟨75609930259364313035417885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50406620172909542023611923 75609930259364313035417885)
      ·
        refine ⟨28353723847261617388281707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75609930259364313035417885 28353723847261617388281707)
        ·
          refine ⟨42530585770892426082422561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28353723847261617388281707 42530585770892426082422561)
          ·
            refine ⟨31897939328169319561816921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42530585770892426082422561 31897939328169319561816921)
            ·
              refine ⟨23923454496126989671362691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31897939328169319561816921 23923454496126989671362691)
              ·
                refine ⟨35885181744190484507044037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23923454496126989671362691 35885181744190484507044037)
                ·
                  refine ⟨6728471577035715845070757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35885181744190484507044037 6728471577035715845070757)
                  ·
                    refine ⟨1261588420694196720950767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6728471577035715845070757 1261588420694196720950767)
                    ·
                      rfl

theorem cell22_3685402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_3685402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685402 prefixEnd_3685402 := by exact prefixLift 3685402
  have htrace : WordTrace (prefixWord ++ tailWord_3685402) baseStart_3685402 baseEnd_3685402 := by
    simpa [prefixWord, tailWord_3685402, baseEnd_3685402] using wordTrace_append hprefix tailTrace_3685402
  have hstable : (prefixWord ++ tailWord_3685402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685402).length < 2 ^ (prefixWord ++ tailWord_3685402).sum := by decide
  have hdescent : baseEnd_3685402 < baseStart_3685402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685477 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 1, 7]
def baseStart_3685477 : Nat := 118140960795 + 3685477 * 2 ^ 59
def prefixEnd_3685477 : Nat := 4983230072969 + 3 ^ 40 * 3685477 * 2
def baseEnd_3685477 : Nat := 1261614094726921525325537

theorem tailTrace_3685477 : CollatzResearch.WordTrace tailWord_3685477 prefixEnd_3685477 1261614094726921525325537 := by
  unfold tailWord_3685477
  simp only [CollatzResearch.WordTrace]
  refine ⟨134420389269153733205278685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89613592846102488803519123 134420389269153733205278685)
  ·
    refine ⟨50407645975932649951979507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134420389269153733205278685 50407645975932649951979507)
    ·
      refine ⟨75611468963898974927969261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50407645975932649951979507 75611468963898974927969261)
      ·
        refine ⟨28354300861462115597988473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75611468963898974927969261 28354300861462115597988473)
        ·
          refine ⟨21265725646096586698491355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28354300861462115597988473 21265725646096586698491355)
          ·
            refine ⟨31898588469144880047737033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21265725646096586698491355 31898588469144880047737033)
            ·
              refine ⟨23923941351858660035802775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31898588469144880047737033 23923941351858660035802775)
              ·
                refine ⟨35885912027787990053704163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23923941351858660035802775 35885912027787990053704163)
                ·
                  refine ⟨53828868041681985080556245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35885912027787990053704163 53828868041681985080556245)
                  ·
                    refine ⟨1261614094726921525325537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53828868041681985080556245 1261614094726921525325537)
                    ·
                      rfl

theorem cell22_3685477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_3685477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685477 prefixEnd_3685477 := by exact prefixLift 3685477
  have htrace : WordTrace (prefixWord ++ tailWord_3685477) baseStart_3685477 baseEnd_3685477 := by
    simpa [prefixWord, tailWord_3685477, baseEnd_3685477] using wordTrace_append hprefix tailTrace_3685477
  have hstable : (prefixWord ++ tailWord_3685477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685477).length < 2 ^ (prefixWord ++ tailWord_3685477).sum := by decide
  have hdescent : baseEnd_3685477 < baseStart_3685477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685479 : List Nat := [1, 1, 5, 1, 1, 4, 1, 3, 5]
def baseStart_3685479 : Nat := 118140960795 + 3685479 * 2 ^ 59
def prefixEnd_3685479 : Nat := 4983230072969 + 3 ^ 40 * 3685479 * 2
def baseEnd_3685479 : Nat := 420538259789264728925177

theorem tailTrace_3685479 : CollatzResearch.WordTrace tailWord_3685479 prefixEnd_3685479 420538259789264728925177 := by
  unfold tailWord_3685479
  simp only [CollatzResearch.WordTrace]
  refine ⟨134420462215146487546851491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89613641476764325031234327 134420462215146487546851491)
  ·
    refine ⟨201630693322719731320277237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134420462215146487546851491 201630693322719731320277237)
    ·
      refine ⟨18902877499004974811275991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201630693322719731320277237 18902877499004974811275991)
      ·
        refine ⟨28354316248507462216913987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18902877499004974811275991 28354316248507462216913987)
        ·
          refine ⟨42531474372761193325370981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28354316248507462216913987 42531474372761193325370981)
          ·
            refine ⟨7974651444892723748507059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42531474372761193325370981 7974651444892723748507059)
            ·
              refine ⟨11961977167339085622760589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7974651444892723748507059 11961977167339085622760589)
              ·
                refine ⟨4485741437752157108535221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11961977167339085622760589 4485741437752157108535221)
                ·
                  refine ⟨420538259789264728925177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4485741437752157108535221 420538259789264728925177)
                  ·
                    rfl

theorem cell22_3685479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 3, 5].length) (baseStart_3685479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685479 prefixEnd_3685479 := by exact prefixLift 3685479
  have htrace : WordTrace (prefixWord ++ tailWord_3685479) baseStart_3685479 baseEnd_3685479 := by
    simpa [prefixWord, tailWord_3685479, baseEnd_3685479] using wordTrace_append hprefix tailTrace_3685479
  have hstable : (prefixWord ++ tailWord_3685479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685479).length < 2 ^ (prefixWord ++ tailWord_3685479).sum := by decide
  have hdescent : baseEnd_3685479 < baseStart_3685479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685554 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_3685554 : Nat := 118140960795 + 3685554 * 2 ^ 59
def prefixEnd_3685554 : Nat := 4983230072969 + 3 ^ 40 * 3685554 * 2
def baseEnd_3685554 : Nat := 1261640453400518991150301

theorem tailTrace_3685554 : CollatzResearch.WordTrace tailWord_3685554 prefixEnd_3685554 1261640453400518991150301 := by
  unfold tailWord_3685554
  simp only [CollatzResearch.WordTrace]
  refine ⟨33605799422468693838957929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89615465126583183570554477 33605799422468693838957929)
  ·
    refine ⟨25204349566851520379218447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33605799422468693838957929 25204349566851520379218447)
    ·
      refine ⟨37806524350277280568827671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25204349566851520379218447 37806524350277280568827671)
      ·
        refine ⟨56709786525415920853241507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37806524350277280568827671 56709786525415920853241507)
        ·
          refine ⟨85064679788123881279862261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56709786525415920853241507 85064679788123881279862261)
          ·
            refine ⟨7974813730136613869987087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85064679788123881279862261 7974813730136613869987087)
            ·
              refine ⟨11962220595204920804980631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7974813730136613869987087 11962220595204920804980631)
              ·
                refine ⟨17943330892807381207470947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11962220595204920804980631 17943330892807381207470947)
                ·
                  refine ⟨26914996339211071811206421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17943330892807381207470947 26914996339211071811206421)
                  ·
                    refine ⟨1261640453400518991150301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26914996339211071811206421 1261640453400518991150301)
                    ·
                      rfl

theorem cell22_3685554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_3685554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685554 prefixEnd_3685554 := by exact prefixLift 3685554
  have htrace : WordTrace (prefixWord ++ tailWord_3685554) baseStart_3685554 baseEnd_3685554 := by
    simpa [prefixWord, tailWord_3685554, baseEnd_3685554] using wordTrace_append hprefix tailTrace_3685554
  have hstable : (prefixWord ++ tailWord_3685554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685554).length < 2 ^ (prefixWord ++ tailWord_3685554).sum := by decide
  have hdescent : baseEnd_3685554 < baseStart_3685554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685590 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_3685590 : Nat := 118140960795 + 3685590 * 2 ^ 59
def prefixEnd_3685590 : Nat := 4983230072969 + 3 ^ 40 * 3685590 * 2
def baseEnd_3685590 : Nat := 1261652776936226897250191

theorem tailTrace_3685590 : CollatzResearch.WordTrace tailWord_3685590 prefixEnd_3685590 1261652776936226897250191 := by
  unfold tailWord_3685590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8401531919859022094008889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89616340478496235669428149 8401531919859022094008889)
  ·
    refine ⟨6301148939894266570506667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8401531919859022094008889 6301148939894266570506667)
    ·
      refine ⟨9451723409841399855760001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6301148939894266570506667 9451723409841399855760001)
      ·
        refine ⟨7088792557381049891820001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9451723409841399855760001 7088792557381049891820001)
        ·
          refine ⟨5316594418035787418865001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7088792557381049891820001 5316594418035787418865001)
          ·
            refine ⟨3987445813526840564148751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5316594418035787418865001 3987445813526840564148751)
            ·
              refine ⟨5981168720290260846223127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3987445813526840564148751 5981168720290260846223127)
              ·
                refine ⟨8971753080435391269334691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981168720290260846223127 8971753080435391269334691)
                ·
                  refine ⟨13457629620653086904002037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8971753080435391269334691 13457629620653086904002037)
                  ·
                    refine ⟨1261652776936226897250191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13457629620653086904002037 1261652776936226897250191)
                    ·
                      rfl

theorem cell22_3685590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_3685590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685590 prefixEnd_3685590 := by exact prefixLift 3685590
  have htrace : WordTrace (prefixWord ++ tailWord_3685590) baseStart_3685590 baseEnd_3685590 := by
    simpa [prefixWord, tailWord_3685590, baseEnd_3685590] using wordTrace_append hprefix tailTrace_3685590
  have hstable : (prefixWord ++ tailWord_3685590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685590).length < 2 ^ (prefixWord ++ tailWord_3685590).sum := by decide
  have hdescent : baseEnd_3685590 < baseStart_3685590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685601 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 3, 3]
def baseStart_3685601 : Nat := 118140960795 + 3685601 * 2 ^ 59
def prefixEnd_3685601 : Nat := 4983230072969 + 3 ^ 40 * 3685601 * 2
def baseEnd_3685601 : Nat := 1261656542461026535225157

theorem tailTrace_3685601 : CollatzResearch.WordTrace tailWord_3685601 prefixEnd_3685601 1261656542461026535225157 := by
  unfold tailWord_3685601
  simp only [CollatzResearch.WordTrace]
  refine ⟨134424911920704502382792657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89616607947136334921861771 134424911920704502382792657)
  ·
    refine ⟨100818683940528376787094493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134424911920704502382792657 100818683940528376787094493)
    ·
      refine ⟨37807006477698141295160435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100818683940528376787094493 37807006477698141295160435)
      ·
        refine ⟨56710509716547211942740653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37807006477698141295160435 56710509716547211942740653)
        ·
          refine ⟨21266441143705204478527745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56710509716547211942740653 21266441143705204478527745)
          ·
            refine ⟨15949830857778903358895809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21266441143705204478527745 15949830857778903358895809)
            ·
              refine ⟨11962373143334177519171857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15949830857778903358895809 11962373143334177519171857)
              ·
                refine ⟨8971779857500633139378893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11962373143334177519171857 8971779857500633139378893)
                ·
                  refine ⟨3364417446562737427267085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8971779857500633139378893 3364417446562737427267085)
                  ·
                    refine ⟨1261656542461026535225157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3364417446562737427267085 1261656542461026535225157)
                    ·
                      rfl

theorem cell22_3685601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 3].length) (baseStart_3685601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685601 prefixEnd_3685601 := by exact prefixLift 3685601
  have htrace : WordTrace (prefixWord ++ tailWord_3685601) baseStart_3685601 baseEnd_3685601 := by
    simpa [prefixWord, tailWord_3685601, baseEnd_3685601] using wordTrace_append hprefix tailTrace_3685601
  have hstable : (prefixWord ++ tailWord_3685601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685601).length < 2 ^ (prefixWord ++ tailWord_3685601).sum := by decide
  have hdescent : baseEnd_3685601 < baseStart_3685601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685614 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 7]
def baseStart_3685614 : Nat := 118140960795 + 3685614 * 2 ^ 59
def prefixEnd_3685614 : Nat := 4983230072969 + 3 ^ 40 * 3685614 * 2
def baseEnd_3685614 : Nat := 420553664208899611550039

theorem tailTrace_3685614 : CollatzResearch.WordTrace tailWord_3685614 prefixEnd_3685614 420553664208899611550039 := by
  unfold tailWord_3685614
  simp only [CollatzResearch.WordTrace]
  refine ⟨16803173258707175700376987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89616924046438270402010597 16803173258707175700376987)
  ·
    refine ⟨25204759888060763550565481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16803173258707175700376987 25204759888060763550565481)
    ·
      refine ⟨18903569916045572662924111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25204759888060763550565481 18903569916045572662924111)
      ·
        refine ⟨28355354874068358994386167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18903569916045572662924111 28355354874068358994386167)
        ·
          refine ⟨42533032311102538491579251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28355354874068358994386167 42533032311102538491579251)
          ·
            refine ⟨63799548466653807737368877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42533032311102538491579251 63799548466653807737368877)
            ·
              refine ⟨23924830674995177901513329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63799548466653807737368877 23924830674995177901513329)
              ·
                refine ⟨17943623006246383426134997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23924830674995177901513329 17943623006246383426134997)
                ·
                  refine ⟨420553664208899611550039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17943623006246383426134997 420553664208899611550039)
                  ·
                    rfl

theorem cell22_3685614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_3685614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685614 prefixEnd_3685614 := by exact prefixLift 3685614
  have htrace : WordTrace (prefixWord ++ tailWord_3685614) baseStart_3685614 baseEnd_3685614 := by
    simpa [prefixWord, tailWord_3685614, baseEnd_3685614] using wordTrace_append hprefix tailTrace_3685614
  have hstable : (prefixWord ++ tailWord_3685614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685614).length < 2 ^ (prefixWord ++ tailWord_3685614).sum := by decide
  have hdescent : baseEnd_3685614 < baseStart_3685614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685620 : List Nat := [2, 6, 1, 2, 1, 2, 8]
def baseStart_3685620 : Nat := 118140960795 + 3685620 * 2 ^ 59
def prefixEnd_3685620 : Nat := 4983230072969 + 3 ^ 40 * 3685620 * 2
def baseEnd_3685620 : Nat := 46728260983308030333337

theorem tailTrace_3685620 : CollatzResearch.WordTrace tailWord_3685620 prefixEnd_3685620 46728260983308030333337 := by
  unfold tailWord_3685620
  simp only [CollatzResearch.WordTrace]
  refine ⟨67212802453817834313867157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89617069938423779085156209 67212802453817834313867157)
  ·
    refine ⟨3150600115022710983462523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67212802453817834313867157 3150600115022710983462523)
    ·
      refine ⟨4725900172534066475193785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3150600115022710983462523 4725900172534066475193785)
      ·
        refine ⟨3544425129400549856395339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4725900172534066475193785 3544425129400549856395339)
        ·
          refine ⟨5316637694100824784593009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3544425129400549856395339 5316637694100824784593009)
          ·
            refine ⟨3987478270575618588444757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5316637694100824784593009 3987478270575618588444757)
            ·
              refine ⟨46728260983308030333337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3987478270575618588444757 46728260983308030333337)
              ·
                rfl

theorem cell22_3685620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 8].length) (baseStart_3685620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685620 prefixEnd_3685620 := by exact prefixLift 3685620
  have htrace : WordTrace (prefixWord ++ tailWord_3685620) baseStart_3685620 baseEnd_3685620 := by
    simpa [prefixWord, tailWord_3685620, baseEnd_3685620] using wordTrace_append hprefix tailTrace_3685620
  have hstable : (prefixWord ++ tailWord_3685620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685620).length < 2 ^ (prefixWord ++ tailWord_3685620).sum := by decide
  have hdescent : baseEnd_3685620 < baseStart_3685620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685635 : List Nat := [1, 1, 1, 3, 2, 5, 3, 2, 1, 3]
def baseStart_3685635 : Nat := 118140960795 + 3685635 * 2 ^ 59
def prefixEnd_3685635 : Nat := 4983230072969 + 3 ^ 40 * 3685635 * 2
def baseEnd_3685635 : Nat := 1261668181355861779875053

theorem tailTrace_3685635 : CollatzResearch.WordTrace tailWord_3685635 prefixEnd_3685635 1261668181355861779875053 := by
  unfold tailWord_3685635
  simp only [CollatzResearch.WordTrace]
  refine ⟨134426152002581326189530359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89617434668387550793020239 134426152002581326189530359)
  ·
    refine ⟨201639228003871989284295539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134426152002581326189530359 201639228003871989284295539)
    ·
      refine ⟨302458842005807983926443309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201639228003871989284295539 302458842005807983926443309)
      ·
        refine ⟨113422065752177993972416241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302458842005807983926443309 113422065752177993972416241)
        ·
          refine ⟨85066549314133495479312181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113422065752177993972416241 85066549314133495479312181)
          ·
            refine ⟨7974988998200015201185517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85066549314133495479312181 7974988998200015201185517)
            ·
              refine ⟨2990620874325005700444569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7974988998200015201185517 2990620874325005700444569)
              ·
                refine ⟨2242965655743754275333427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2990620874325005700444569 2242965655743754275333427)
                ·
                  refine ⟨3364448483615631413000141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242965655743754275333427 3364448483615631413000141)
                  ·
                    refine ⟨1261668181355861779875053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3364448483615631413000141 1261668181355861779875053)
                    ·
                      rfl

theorem cell22_3685635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 1, 3].length) (baseStart_3685635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685635 prefixEnd_3685635 := by exact prefixLift 3685635
  have htrace : WordTrace (prefixWord ++ tailWord_3685635) baseStart_3685635 baseEnd_3685635 := by
    simpa [prefixWord, tailWord_3685635, baseEnd_3685635] using wordTrace_append hprefix tailTrace_3685635
  have hstable : (prefixWord ++ tailWord_3685635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685635).length < 2 ^ (prefixWord ++ tailWord_3685635).sum := by decide
  have hdescent : baseEnd_3685635 < baseStart_3685635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685676 : List Nat := [2, 2, 1, 1, 1, 3, 1, 7, 4]
def baseStart_3685676 : Nat := 118140960795 + 3685676 * 2 ^ 59
def prefixEnd_3685676 : Nat := 4983230072969 + 3 ^ 40 * 3685676 * 2
def baseEnd_3685676 : Nat := 420560738831250446533309

theorem tailTrace_3685676 : CollatzResearch.WordTrace tailWord_3685676 prefixEnd_3685676 420560738831250446533309 := by
  unfold tailWord_3685676
  simp only [CollatzResearch.WordTrace]
  refine ⟨67213823697716395095886441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89618431596955193461181921 67213823697716395095886441)
  ·
    refine ⟨50410367773287296321914831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67213823697716395095886441 50410367773287296321914831)
    ·
      refine ⟨75615551659930944482872247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50410367773287296321914831 75615551659930944482872247)
      ·
        refine ⟨113423327489896416724308371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75615551659930944482872247 113423327489896416724308371)
        ·
          refine ⟨170134991234844625086462557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113423327489896416724308371 170134991234844625086462557)
          ·
            refine ⟨63800621713066734407423459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170134991234844625086462557 63800621713066734407423459)
            ·
              refine ⟨95700932569600101611135189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63800621713066734407423459 95700932569600101611135189)
              ·
                refine ⟨2242990607100002381510981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95700932569600101611135189 2242990607100002381510981)
                ·
                  refine ⟨420560738831250446533309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2242990607100002381510981 420560738831250446533309)
                  ·
                    rfl

theorem cell22_3685676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 7, 4].length) (baseStart_3685676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685676 prefixEnd_3685676 := by exact prefixLift 3685676
  have htrace : WordTrace (prefixWord ++ tailWord_3685676) baseStart_3685676 baseEnd_3685676 := by
    simpa [prefixWord, tailWord_3685676, baseEnd_3685676] using wordTrace_append hprefix tailTrace_3685676
  have hstable : (prefixWord ++ tailWord_3685676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685676).length < 2 ^ (prefixWord ++ tailWord_3685676).sum := by decide
  have hdescent : baseEnd_3685676 < baseStart_3685676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685686 : List Nat := [5, 1, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_3685686 : Nat := 118140960795 + 3685686 * 2 ^ 59
def prefixEnd_3685686 : Nat := 4983230072969 + 3 ^ 40 * 3685686 * 2
def baseEnd_3685686 : Nat := 1261685639698114646849897

theorem tailTrace_3685686 : CollatzResearch.WordTrace tailWord_3685686 prefixEnd_3685686 1261685639698114646849897 := by
  unfold tailWord_3685686
  simp only [CollatzResearch.WordTrace]
  refine ⟨8401750757837285118727307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89618674750264374599757941 8401750757837285118727307)
  ·
    refine ⟨12602626136755927678090961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8401750757837285118727307 12602626136755927678090961)
    ·
      refine ⟨9451969602566945758568221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12602626136755927678090961 9451969602566945758568221)
      ·
        refine ⟨3544488600962604659463083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9451969602566945758568221 3544488600962604659463083)
        ·
          refine ⟨5316732901443906989194625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3544488600962604659463083 5316732901443906989194625)
          ·
            refine ⟨3987549676082930241895969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5316732901443906989194625 3987549676082930241895969)
            ·
              refine ⟨2990662257062197681421977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3987549676082930241895969 2990662257062197681421977)
              ·
                refine ⟨2242996692796648261066483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2990662257062197681421977 2242996692796648261066483)
                ·
                  refine ⟨3364495039194972391599725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2242996692796648261066483 3364495039194972391599725)
                  ·
                    refine ⟨1261685639698114646849897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3364495039194972391599725 1261685639698114646849897)
                    ·
                      rfl

theorem cell22_3685686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_3685686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685686 prefixEnd_3685686 := by exact prefixLift 3685686
  have htrace : WordTrace (prefixWord ++ tailWord_3685686) baseStart_3685686 baseEnd_3685686 := by
    simpa [prefixWord, tailWord_3685686, baseEnd_3685686] using wordTrace_append hprefix tailTrace_3685686
  have hstable : (prefixWord ++ tailWord_3685686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685686).length < 2 ^ (prefixWord ++ tailWord_3685686).sum := by decide
  have hdescent : baseEnd_3685686 < baseStart_3685686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685708 : List Nat := [2, 2, 1, 3, 2, 2, 2, 3, 2, 3]
def baseStart_3685708 : Nat := 118140960795 + 3685708 * 2 ^ 59
def prefixEnd_3685708 : Nat := 4983230072969 + 3 ^ 40 * 3685708 * 2
def baseEnd_3685708 : Nat := 1261693170747713922799829

theorem tailTrace_3685708 : CollatzResearch.WordTrace tailWord_3685708 prefixEnd_3685708 1261693170747713922799829 := by
  unfold tailWord_3685708
  simp only [CollatzResearch.WordTrace]
  refine ⟨67214407265658429828468889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89619209687544573104625185 67214407265658429828468889)
  ·
    refine ⟨50410805449243822371351667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67214407265658429828468889 50410805449243822371351667)
    ·
      refine ⟨75616208173865733557027501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50410805449243822371351667 75616208173865733557027501)
      ·
        refine ⟨28356078065199650083885313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75616208173865733557027501 28356078065199650083885313)
        ·
          refine ⟨21267058548899737562913985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28356078065199650083885313 21267058548899737562913985)
          ·
            refine ⟨15950293911674803172185489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21267058548899737562913985 15950293911674803172185489)
            ·
              refine ⟨11962720433756102379139117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15950293911674803172185489 11962720433756102379139117)
              ·
                refine ⟨4486020162658538392177169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11962720433756102379139117 4486020162658538392177169)
                ·
                  refine ⟨3364515121993903794132877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4486020162658538392177169 3364515121993903794132877)
                  ·
                    refine ⟨1261693170747713922799829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3364515121993903794132877 1261693170747713922799829)
                    ·
                      rfl

theorem cell22_3685708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_3685708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685708 prefixEnd_3685708 := by exact prefixLift 3685708
  have htrace : WordTrace (prefixWord ++ tailWord_3685708) baseStart_3685708 baseEnd_3685708 := by
    simpa [prefixWord, tailWord_3685708, baseEnd_3685708] using wordTrace_append hprefix tailTrace_3685708
  have hstable : (prefixWord ++ tailWord_3685708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685708).length < 2 ^ (prefixWord ++ tailWord_3685708).sum := by decide
  have hdescent : baseEnd_3685708 < baseStart_3685708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685779 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 4, 8]
def baseStart_3685779 : Nat := 118140960795 + 3685779 * 2 ^ 59
def prefixEnd_3685779 : Nat := 4983230072969 + 3 ^ 40 * 3685779 * 2
def baseEnd_3685779 : Nat := 1261717475498693404274611

theorem tailTrace_3685779 : CollatzResearch.WordTrace tailWord_3685779 prefixEnd_3685779 1261717475498693404274611 := by
  unfold tailWord_3685779
  simp only [CollatzResearch.WordTrace]
  refine ⟨134431404114059638782772391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89620936076039759188514927 134431404114059638782772391)
  ·
    refine ⟨201647106171089458174158587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134431404114059638782772391 201647106171089458174158587)
    ·
      refine ⟨302470659256634187261237881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201647106171089458174158587 302470659256634187261237881)
      ·
        refine ⟨226852994442475640445928411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302470659256634187261237881 226852994442475640445928411)
        ·
          refine ⟨340279491663713460668892617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226852994442475640445928411 340279491663713460668892617)
          ·
            refine ⟨255209618747785095501669463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340279491663713460668892617 255209618747785095501669463)
            ·
              refine ⟨382814428121677643252504195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255209618747785095501669463 382814428121677643252504195)
              ·
                refine ⟨574221642182516464878756293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 382814428121677643252504195 574221642182516464878756293)
                ·
                  refine ⟨107666557909221837164766805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 574221642182516464878756293 107666557909221837164766805)
                  ·
                    refine ⟨1261717475498693404274611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107666557909221837164766805 1261717475498693404274611)
                    ·
                      rfl

theorem cell22_3685779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 8].length) (baseStart_3685779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685779 prefixEnd_3685779 := by exact prefixLift 3685779
  have htrace : WordTrace (prefixWord ++ tailWord_3685779) baseStart_3685779 baseEnd_3685779 := by
    simpa [prefixWord, tailWord_3685779, baseEnd_3685779] using wordTrace_append hprefix tailTrace_3685779
  have hstable : (prefixWord ++ tailWord_3685779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685779).length < 2 ^ (prefixWord ++ tailWord_3685779).sum := by decide
  have hdescent : baseEnd_3685779 < baseStart_3685779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685796 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 5, 4]
def baseStart_3685796 : Nat := 118140960795 + 3685796 * 2 ^ 59
def prefixEnd_3685796 : Nat := 4983230072969 + 3 ^ 40 * 3685796 * 2
def baseEnd_3685796 : Nat := 1261723294946111026599559

theorem tailTrace_3685796 : CollatzResearch.WordTrace tailWord_3685796 prefixEnd_3685796 1261723294946111026599559 := by
  unfold tailWord_3685796
  simp only [CollatzResearch.WordTrace]
  refine ⟨67216012077499025343070621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89621349436665367124094161 67216012077499025343070621)
  ·
    refine ⟨25206004529062134503651483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67216012077499025343070621 25206004529062134503651483)
    ·
      refine ⟨37809006793593201755477225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25206004529062134503651483 37809006793593201755477225)
      ·
        refine ⟨28356755095194901316607919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37809006793593201755477225 28356755095194901316607919)
        ·
          refine ⟨42535132642792351974911879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28356755095194901316607919 42535132642792351974911879)
          ·
            refine ⟨63802698964188527962367819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42535132642792351974911879 63802698964188527962367819)
            ·
              refine ⟨95704048446282791943551729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63802698964188527962367819 95704048446282791943551729)
              ·
                refine ⟨71778036334712093957663797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95704048446282791943551729 71778036334712093957663797)
                ·
                  refine ⟨6729190906379258808530981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71778036334712093957663797 6729190906379258808530981)
                  ·
                    refine ⟨1261723294946111026599559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6729190906379258808530981 1261723294946111026599559)
                    ·
                      rfl

theorem cell22_3685796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_3685796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685796 prefixEnd_3685796 := by exact prefixLift 3685796
  have htrace : WordTrace (prefixWord ++ tailWord_3685796) baseStart_3685796 baseEnd_3685796 := by
    simpa [prefixWord, tailWord_3685796, baseEnd_3685796] using wordTrace_append hprefix tailTrace_3685796
  have hstable : (prefixWord ++ tailWord_3685796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685796).length < 2 ^ (prefixWord ++ tailWord_3685796).sum := by decide
  have hdescent : baseEnd_3685796 < baseStart_3685796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685817 : List Nat := [1, 2, 1, 4, 5, 1, 2, 1, 5]
def baseStart_3685817 : Nat := 118140960795 + 3685817 * 2 ^ 59
def prefixEnd_3685817 : Nat := 4983230072969 + 3 ^ 40 * 3685817 * 2
def baseEnd_3685817 : Nat := 420576827891757990608165

theorem tailTrace_3685817 : CollatzResearch.WordTrace tailWord_3685817 prefixEnd_3685817 420576827891757990608165 := by
  unfold tailWord_3685817
  simp only [CollatzResearch.WordTrace]
  refine ⟨134432790087921971272655705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89621860058614647515103803 134432790087921971272655705)
  ·
    refine ⟨100824592565941478454491779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134432790087921971272655705 100824592565941478454491779)
    ·
      refine ⟨151236888848912217681737669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100824592565941478454491779 151236888848912217681737669)
      ·
        refine ⟨28356916659171040815325813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151236888848912217681737669 28356916659171040815325813)
        ·
          refine ⟨2658460936797285076436795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28356916659171040815325813 2658460936797285076436795)
          ·
            refine ⟨3987691405195927614655193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2658460936797285076436795 3987691405195927614655193)
            ·
              refine ⟨2990768553896945710991395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3987691405195927614655193 2990768553896945710991395)
              ·
                refine ⟨4486152830845418566487093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2990768553896945710991395 4486152830845418566487093)
                ·
                  refine ⟨420576827891757990608165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4486152830845418566487093 420576827891757990608165)
                  ·
                    rfl

theorem cell22_3685817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 1, 5].length) (baseStart_3685817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685817 prefixEnd_3685817 := by exact prefixLift 3685817
  have htrace : WordTrace (prefixWord ++ tailWord_3685817) baseStart_3685817 baseEnd_3685817 := by
    simpa [prefixWord, tailWord_3685817, baseEnd_3685817] using wordTrace_append hprefix tailTrace_3685817
  have hstable : (prefixWord ++ tailWord_3685817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685817).length < 2 ^ (prefixWord ++ tailWord_3685817).sum := by decide
  have hdescent : baseEnd_3685817 < baseStart_3685817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685873 : List Nat := [1, 2, 2, 2, 3, 4, 1, 7]
def baseStart_3685873 : Nat := 118140960795 + 3685873 * 2 ^ 59
def prefixEnd_3685873 : Nat := 4983230072969 + 3 ^ 40 * 3685873 * 2
def baseEnd_3685873 : Nat := 140194405957745388047147

theorem tailTrace_3685873 : CollatzResearch.WordTrace tailWord_3685873 prefixEnd_3685873 140194405957745388047147 := by
  unfold tailWord_3685873
  simp only [CollatzResearch.WordTrace]
  refine ⟨134434832575719092836694273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89623221717146061891129515 134434832575719092836694273)
  ·
    refine ⟨100826124431789319627520705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134434832575719092836694273 100826124431789319627520705)
    ·
      refine ⟨75619593323841989720640529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100826124431789319627520705 75619593323841989720640529)
      ·
        refine ⟨56714694992881492290480397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75619593323841989720640529 56714694992881492290480397)
        ·
          refine ⟨21268010622330559608930149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56714694992881492290480397 21268010622330559608930149)
          ·
            refine ⟨3987751991686979926674403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21268010622330559608930149 3987751991686979926674403)
            ·
              refine ⟨5981627987530469890011605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3987751991686979926674403 5981627987530469890011605)
              ·
                refine ⟨140194405957745388047147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5981627987530469890011605 140194405957745388047147)
                ·
                  rfl

theorem cell22_3685873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 7].length) (baseStart_3685873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685873 prefixEnd_3685873 := by exact prefixLift 3685873
  have htrace : WordTrace (prefixWord ++ tailWord_3685873) baseStart_3685873 baseEnd_3685873 := by
    simpa [prefixWord, tailWord_3685873, baseEnd_3685873] using wordTrace_append hprefix tailTrace_3685873
  have hstable : (prefixWord ++ tailWord_3685873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685873).length < 2 ^ (prefixWord ++ tailWord_3685873).sum := by decide
  have hdescent : baseEnd_3685873 < baseStart_3685873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685877 : List Nat := [1, 3, 5, 1, 1, 1, 2, 3, 2, 3]
def baseStart_3685877 : Nat := 118140960795 + 3685877 * 2 ^ 59
def prefixEnd_3685877 : Nat := 4983230072969 + 3 ^ 40 * 3685877 * 2
def baseEnd_3685877 : Nat := 1261751022901453815324311

theorem tailTrace_3685877 : CollatzResearch.WordTrace tailWord_3685877 prefixEnd_3685877 1261751022901453815324311 := by
  unfold tailWord_3685877
  simp only [CollatzResearch.WordTrace]
  refine ⟨134434978467704601519839885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89623318978469734346559923 134434978467704601519839885)
  ·
    refine ⟨50413116925389225569939957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134434978467704601519839885 50413116925389225569939957)
    ·
      refine ⟨4726229711755239897181871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50413116925389225569939957 4726229711755239897181871)
      ·
        refine ⟨7089344567632859845772807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4726229711755239897181871 7089344567632859845772807)
        ·
          refine ⟨10634016851449289768659211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7089344567632859845772807 10634016851449289768659211)
          ·
            refine ⟨15951025277173934652988817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10634016851449289768659211 15951025277173934652988817)
            ·
              refine ⟨11963268957880450989741613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15951025277173934652988817 11963268957880450989741613)
              ·
                refine ⟨4486225859205169121153105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11963268957880450989741613 4486225859205169121153105)
                ·
                  refine ⟨3364669394403876840864829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4486225859205169121153105 3364669394403876840864829)
                  ·
                    refine ⟨1261751022901453815324311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3364669394403876840864829 1261751022901453815324311)
                    ·
                      rfl

theorem cell22_3685877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_3685877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685877 prefixEnd_3685877 := by exact prefixLift 3685877
  have htrace : WordTrace (prefixWord ++ tailWord_3685877) baseStart_3685877 baseEnd_3685877 := by
    simpa [prefixWord, tailWord_3685877, baseEnd_3685877] using wordTrace_append hprefix tailTrace_3685877
  have hstable : (prefixWord ++ tailWord_3685877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685877).length < 2 ^ (prefixWord ++ tailWord_3685877).sum := by decide
  have hdescent : baseEnd_3685877 < baseStart_3685877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685892 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 2, 4]
def baseStart_3685892 : Nat := 118140960795 + 3685892 * 2 ^ 59
def prefixEnd_3685892 : Nat := 4983230072969 + 3 ^ 40 * 3685892 * 2
def baseEnd_3685892 : Nat := 1261756157707998776199265

theorem tailTrace_3685892 : CollatzResearch.WordTrace tailWord_3685892 prefixEnd_3685892 1261756157707998776199265 := by
  unfold tailWord_3685892
  simp only [CollatzResearch.WordTrace]
  refine ⟨67217762781325129540817965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89623683708433506054423953 67217762781325129540817965)
  ·
    refine ⟨25206661042996923577806737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67217762781325129540817965 25206661042996923577806737)
    ·
      refine ⟨18904995782247692683355053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25206661042996923577806737 18904995782247692683355053)
      ·
        refine ⟨7089373418342884756258145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18904995782247692683355053 7089373418342884756258145)
        ·
          refine ⟨5317030063757163567193609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7089373418342884756258145 5317030063757163567193609)
          ·
            refine ⟨3987772547817872675395207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5317030063757163567193609 3987772547817872675395207)
            ·
              refine ⟨5981658821726809013092811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3987772547817872675395207 5981658821726809013092811)
              ·
                refine ⟨8972488232590213519639217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981658821726809013092811 8972488232590213519639217)
                ·
                  refine ⟨6729366174442660139729413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8972488232590213519639217 6729366174442660139729413)
                  ·
                    refine ⟨1261756157707998776199265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6729366174442660139729413 1261756157707998776199265)
                    ·
                      rfl

theorem cell22_3685892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_3685892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685892 prefixEnd_3685892 := by exact prefixLift 3685892
  have htrace : WordTrace (prefixWord ++ tailWord_3685892) baseStart_3685892 baseEnd_3685892 := by
    simpa [prefixWord, tailWord_3685892, baseEnd_3685892] using wordTrace_append hprefix tailTrace_3685892
  have hstable : (prefixWord ++ tailWord_3685892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685892).length < 2 ^ (prefixWord ++ tailWord_3685892).sum := by decide
  have hdescent : baseEnd_3685892 < baseStart_3685892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685922 : List Nat := [3, 3, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_3685922 : Nat := 118140960795 + 3685922 * 2 ^ 59
def prefixEnd_3685922 : Nat := 4983230072969 + 3 ^ 40 * 3685922 * 2
def baseEnd_3685922 : Nat := 1261766427321088697949173

theorem tailTrace_3685922 : CollatzResearch.WordTrace tailWord_3685922 prefixEnd_3685922 1261766427321088697949173 := by
  unfold tailWord_3685922
  simp only [CollatzResearch.WordTrace]
  refine ⟨33609154938135393551307005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89624413168361049470152013 33609154938135393551307005)
  ·
    refine ⟨12603433101800772581740127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33609154938135393551307005 12603433101800772581740127)
    ·
      refine ⟨18905149652701158872610191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12603433101800772581740127 18905149652701158872610191)
      ·
        refine ⟨28357724479051738308915287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18905149652701158872610191 28357724479051738308915287)
        ·
          refine ⟨42536586718577607463372931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28357724479051738308915287 42536586718577607463372931)
          ·
            refine ⟨63804880077866411195059397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42536586718577607463372931 63804880077866411195059397)
            ·
              refine ⟨11963415014599952099073637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63804880077866411195059397 11963415014599952099073637)
              ·
                refine ⟨2243140315237491018576307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11963415014599952099073637 2243140315237491018576307)
                ·
                  refine ⟨3364710472856236527864461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243140315237491018576307 3364710472856236527864461)
                  ·
                    refine ⟨1261766427321088697949173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3364710472856236527864461 1261766427321088697949173)
                    ·
                      rfl

theorem cell22_3685922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_3685922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685922 prefixEnd_3685922 := by exact prefixLift 3685922
  have htrace : WordTrace (prefixWord ++ tailWord_3685922) baseStart_3685922 baseEnd_3685922 := by
    simpa [prefixWord, tailWord_3685922, baseEnd_3685922] using wordTrace_append hprefix tailTrace_3685922
  have hstable : (prefixWord ++ tailWord_3685922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685922).length < 2 ^ (prefixWord ++ tailWord_3685922).sum := by decide
  have hdescent : baseEnd_3685922 < baseStart_3685922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3685980 : List Nat := [2, 2, 4, 1, 2, 1, 3, 1, 6]
def baseStart_3685980 : Nat := 118140960795 + 3685980 * 2 ^ 59
def prefixEnd_3685980 : Nat := 4983230072969 + 3 ^ 40 * 3685980 * 2
def baseEnd_3685980 : Nat := 420595427302131959999665

theorem tailTrace_3685980 : CollatzResearch.WordTrace tailWord_3685980 prefixEnd_3685980 420595427302131959999665 := by
  unfold tailWord_3685980
  simp only [CollatzResearch.WordTrace]
  refine ⟨67219367593165725055419697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89625823457554300073892929 67219367593165725055419697)
  ·
    refine ⟨50414525694874293791564773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67219367593165725055419697 50414525694874293791564773)
    ·
      refine ⟨9452723567788930085918395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50414525694874293791564773 9452723567788930085918395)
      ·
        refine ⟨14179085351683395128877593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9452723567788930085918395 14179085351683395128877593)
        ·
          refine ⟨10634314013762546346658195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14179085351683395128877593 10634314013762546346658195)
          ·
            refine ⟨15951471020643819519987293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10634314013762546346658195 15951471020643819519987293)
            ·
              refine ⟨5981801632741432319995235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15951471020643819519987293 5981801632741432319995235)
              ·
                refine ⟨8972702449112148479992853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5981801632741432319995235 8972702449112148479992853)
                ·
                  refine ⟨420595427302131959999665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8972702449112148479992853 420595427302131959999665)
                  ·
                    rfl

theorem cell22_3685980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_3685980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3685980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3685980 prefixEnd_3685980 := by exact prefixLift 3685980
  have htrace : WordTrace (prefixWord ++ tailWord_3685980) baseStart_3685980 baseEnd_3685980 := by
    simpa [prefixWord, tailWord_3685980, baseEnd_3685980] using wordTrace_append hprefix tailTrace_3685980
  have hstable : (prefixWord ++ tailWord_3685980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3685980).length < 2 ^ (prefixWord ++ tailWord_3685980).sum := by decide
  have hdescent : baseEnd_3685980 < baseStart_3685980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3685980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686074 : List Nat := [3, 1, 1, 1, 2, 5, 2, 3, 1, 3]
def baseStart_3686074 : Nat := 118140960795 + 3686074 * 2 ^ 59
def prefixEnd_3686074 : Nat := 4983230072969 + 3 ^ 40 * 3686074 * 2
def baseEnd_3686074 : Nat := 1261818460027410968148707

theorem tailTrace_3686074 : CollatzResearch.WordTrace tailWord_3686074 prefixEnd_3686074 1261818460027410968148707 := by
  unfold tailWord_3686074
  simp only [CollatzResearch.WordTrace]
  refine ⟨33610540911997726041190319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89628109098660602776507517 33610540911997726041190319)
  ·
    refine ⟨50415811367996589061785479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33610540911997726041190319 50415811367996589061785479)
    ·
      refine ⟨75623717051994883592678219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50415811367996589061785479 75623717051994883592678219)
      ·
        refine ⟨113435575577992325389017329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75623717051994883592678219 113435575577992325389017329)
        ·
          refine ⟨85076681683494244041762997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113435575577992325389017329 85076681683494244041762997)
          ·
            refine ⟨7975938907827585378915281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85076681683494244041762997 7975938907827585378915281)
            ·
              refine ⟨5981954180870689034186461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7975938907827585378915281 5981954180870689034186461)
              ·
                refine ⟨2243232817826508387819923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5981954180870689034186461 2243232817826508387819923)
                ·
                  refine ⟨3364849226739762581729885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243232817826508387819923 3364849226739762581729885)
                  ·
                    refine ⟨1261818460027410968148707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3364849226739762581729885 1261818460027410968148707)
                    ·
                      rfl

theorem cell22_3686074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_3686074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686074 prefixEnd_3686074 := by exact prefixLift 3686074
  have htrace : WordTrace (prefixWord ++ tailWord_3686074) baseStart_3686074 baseEnd_3686074 := by
    simpa [prefixWord, tailWord_3686074, baseEnd_3686074] using wordTrace_append hprefix tailTrace_3686074
  have hstable : (prefixWord ++ tailWord_3686074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686074).length < 2 ^ (prefixWord ++ tailWord_3686074).sum := by decide
  have hdescent : baseEnd_3686074 < baseStart_3686074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686117 : List Nat := [1, 3, 1, 4, 1, 1, 4, 2, 1, 4]
def baseStart_3686117 : Nat := 118140960795 + 3686117 * 2 ^ 59
def prefixEnd_3686117 : Nat := 4983230072969 + 3 ^ 40 * 3686117 * 2
def baseEnd_3686117 : Nat := 1261833179806173189323575

theorem tailTrace_3686117 : CollatzResearch.WordTrace tailWord_3686117 prefixEnd_3686117 1261833179806173189323575 := by
  unfold tailWord_3686117
  simp only [CollatzResearch.WordTrace]
  refine ⟨134443731986835122508576605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89629154657890081672384403 134443731986835122508576605)
  ·
    refine ⟨50416399495063170940716227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134443731986835122508576605 50416399495063170940716227)
    ·
      refine ⟨75624599242594756411074341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50416399495063170940716227 75624599242594756411074341)
      ·
        refine ⟨14179612357986516827076439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75624599242594756411074341 14179612357986516827076439)
        ·
          refine ⟨21269418536979775240614659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14179612357986516827076439 21269418536979775240614659)
          ·
            refine ⟨31904127805469662860921989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21269418536979775240614659 31904127805469662860921989)
            ·
              refine ⟨5982023963525561786422873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31904127805469662860921989 5982023963525561786422873)
              ·
                refine ⟨4486517972644171339817155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5982023963525561786422873 4486517972644171339817155)
                ·
                  refine ⟨6729776958966257009725733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4486517972644171339817155 6729776958966257009725733)
                  ·
                    refine ⟨1261833179806173189323575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6729776958966257009725733 1261833179806173189323575)
                    ·
                      rfl

theorem cell22_3686117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_3686117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686117 prefixEnd_3686117 := by exact prefixLift 3686117
  have htrace : WordTrace (prefixWord ++ tailWord_3686117) baseStart_3686117 baseEnd_3686117 := by
    simpa [prefixWord, tailWord_3686117, baseEnd_3686117] using wordTrace_append hprefix tailTrace_3686117
  have hstable : (prefixWord ++ tailWord_3686117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686117).length < 2 ^ (prefixWord ++ tailWord_3686117).sum := by decide
  have hdescent : baseEnd_3686117 < baseStart_3686117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686130 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_3686130 : Nat := 118140960795 + 3686130 * 2 ^ 59
def prefixEnd_3686130 : Nat := 4983230072969 + 3 ^ 40 * 3686130 * 2
def baseEnd_3686130 : Nat := 1261837629971845488748535

theorem tailTrace_3686130 : CollatzResearch.WordTrace tailWord_3686130 prefixEnd_3686130 1261837629971845488748535 := by
  unfold tailWord_3686130
  simp only [CollatzResearch.WordTrace]
  refine ⟨33611051533947006432199961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89629470757192017152533229 33611051533947006432199961)
  ·
    refine ⟨25208288650460254824149971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33611051533947006432199961 25208288650460254824149971)
    ·
      refine ⟨37812432975690382236224957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25208288650460254824149971 37812432975690382236224957)
      ·
        refine ⟨14179662365883893338584359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37812432975690382236224957 14179662365883893338584359)
        ·
          refine ⟨21269493548825840007876539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14179662365883893338584359 21269493548825840007876539)
          ·
            refine ⟨31904240323238760011814809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21269493548825840007876539 31904240323238760011814809)
            ·
              refine ⟨23928180242429070008861107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31904240323238760011814809 23928180242429070008861107)
              ·
                refine ⟨35892270363643605013291661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23928180242429070008861107 35892270363643605013291661)
                ·
                  refine ⟨13459601386366351879984373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35892270363643605013291661 13459601386366351879984373)
                  ·
                    refine ⟨1261837629971845488748535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13459601386366351879984373 1261837629971845488748535)
                    ·
                      rfl

theorem cell22_3686130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_3686130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686130 prefixEnd_3686130 := by exact prefixLift 3686130
  have htrace : WordTrace (prefixWord ++ tailWord_3686130) baseStart_3686130 baseEnd_3686130 := by
    simpa [prefixWord, tailWord_3686130, baseEnd_3686130] using wordTrace_append hprefix tailTrace_3686130
  have hstable : (prefixWord ++ tailWord_3686130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686130).length < 2 ^ (prefixWord ++ tailWord_3686130).sum := by decide
  have hdescent : baseEnd_3686130 < baseStart_3686130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686143 : List Nat := [1, 1, 2, 2, 1, 3, 12]
def baseStart_3686143 : Nat := 118140960795 + 3686143 * 2 ^ 59
def prefixEnd_3686143 : Nat := 4983230072969 + 3 ^ 40 * 3686143 * 2
def baseEnd_3686143 : Nat := 46734891856945103265685

theorem tailTrace_3686143 : CollatzResearch.WordTrace tailWord_3686143 prefixEnd_3686143 46734891856945103265685 := by
  unfold tailWord_3686143
  simp only [CollatzResearch.WordTrace]
  refine ⟨134444680284740928949023083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89629786856493952632682055 134444680284740928949023083)
  ·
    refine ⟨201667020427111393423534625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134444680284740928949023083 201667020427111393423534625)
    ·
      refine ⟨151250265320333545067650969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201667020427111393423534625 151250265320333545067650969)
      ·
        refine ⟨113437698990250158800738227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151250265320333545067650969 113437698990250158800738227)
        ·
          refine ⟨170156548485375238201107341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113437698990250158800738227 170156548485375238201107341)
          ·
            refine ⟨63808705682015714325415253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170156548485375238201107341 63808705682015714325415253)
            ·
              refine ⟨46734891856945103265685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 63808705682015714325415253 46734891856945103265685)
              ·
                rfl

theorem cell22_3686143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 12].length) (baseStart_3686143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686143 prefixEnd_3686143 := by exact prefixLift 3686143
  have htrace : WordTrace (prefixWord ++ tailWord_3686143) baseStart_3686143 baseEnd_3686143 := by
    simpa [prefixWord, tailWord_3686143, baseEnd_3686143] using wordTrace_append hprefix tailTrace_3686143
  have hstable : (prefixWord ++ tailWord_3686143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686143).length < 2 ^ (prefixWord ++ tailWord_3686143).sum := by decide
  have hdescent : baseEnd_3686143 < baseStart_3686143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686145 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3686145 : Nat := 118140960795 + 3686145 * 2 ^ 59
def prefixEnd_3686145 : Nat := 4983230072969 + 3 ^ 40 * 3686145 * 2
def baseEnd_3686145 : Nat := 1261842764778390449623489

theorem tailTrace_3686145 : CollatzResearch.WordTrace tailWord_3686145 prefixEnd_3686145 1261842764778390449623489 := by
  unfold tailWord_3686145
  simp only [CollatzResearch.WordTrace]
  refine ⟨134444753230733683290595889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89629835487155788860397259 134444753230733683290595889)
  ·
    refine ⟨100833564923050262467946917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134444753230733683290595889 100833564923050262467946917)
    ·
      refine ⟨18906293423071924212740047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100833564923050262467946917 18906293423071924212740047)
      ·
        refine ⟨28359440134607886319110071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18906293423071924212740047 28359440134607886319110071)
        ·
          refine ⟨42539160201911829478665107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28359440134607886319110071 42539160201911829478665107)
          ·
            refine ⟨63808740302867744217997661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42539160201911829478665107 63808740302867744217997661)
            ·
              refine ⟨23928277613575404081749123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63808740302867744217997661 23928277613575404081749123)
              ·
                refine ⟨35892416420363106122623685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23928277613575404081749123 35892416420363106122623685)
                ·
                  refine ⟨6729828078818082397991941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35892416420363106122623685 6729828078818082397991941)
                  ·
                    refine ⟨1261842764778390449623489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6729828078818082397991941 1261842764778390449623489)
                    ·
                      rfl

theorem cell22_3686145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3686145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686145 prefixEnd_3686145 := by exact prefixLift 3686145
  have htrace : WordTrace (prefixWord ++ tailWord_3686145) baseStart_3686145 baseEnd_3686145 := by
    simpa [prefixWord, tailWord_3686145, baseEnd_3686145] using wordTrace_append hprefix tailTrace_3686145
  have hstable : (prefixWord ++ tailWord_3686145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686145).length < 2 ^ (prefixWord ++ tailWord_3686145).sum := by decide
  have hdescent : baseEnd_3686145 < baseStart_3686145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686294 : List Nat := [5, 3, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_3686294 : Nat := 118140960795 + 3686294 * 2 ^ 59
def prefixEnd_3686294 : Nat := 4983230072969 + 3 ^ 40 * 3686294 * 2
def baseEnd_3686294 : Nat := 1261893770523403727648033

theorem tailTrace_3686294 : CollatzResearch.WordTrace tailWord_3686294 prefixEnd_3686294 1261893770523403727648033 := by
  unfold tailWord_3686294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8403136731699617608610621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89633458471462587825179957 8403136731699617608610621)
  ·
    refine ⟨3151176274387356603228983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8403136731699617608610621 3151176274387356603228983)
    ·
      refine ⟨4726764411581034904843475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3151176274387356603228983 4726764411581034904843475)
      ·
        refine ⟨7090146617371552357265213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4726764411581034904843475 7090146617371552357265213)
        ·
          refine ⟨2658804981514332133974455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7090146617371552357265213 2658804981514332133974455)
          ·
            refine ⟨3988207472271498200961683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2658804981514332133974455 3988207472271498200961683)
            ·
              refine ⟨5982311208407247301442525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3988207472271498200961683 5982311208407247301442525)
              ·
                refine ⟨2243366703152717738040947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5982311208407247301442525 2243366703152717738040947)
                ·
                  refine ⟨3365050054729076607061421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243366703152717738040947 3365050054729076607061421)
                  ·
                    refine ⟨1261893770523403727648033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3365050054729076607061421 1261893770523403727648033)
                    ·
                      rfl

theorem cell22_3686294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_3686294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686294 prefixEnd_3686294 := by exact prefixLift 3686294
  have htrace : WordTrace (prefixWord ++ tailWord_3686294) baseStart_3686294 baseEnd_3686294 := by
    simpa [prefixWord, tailWord_3686294, baseEnd_3686294] using wordTrace_append hprefix tailTrace_3686294
  have hstable : (prefixWord ++ tailWord_3686294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686294).length < 2 ^ (prefixWord ++ tailWord_3686294).sum := by decide
  have hdescent : baseEnd_3686294 < baseStart_3686294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686301 : List Nat := [1, 4, 2, 1, 2, 4, 1, 3, 4]
def baseStart_3686301 : Nat := 118140960795 + 3686301 * 2 ^ 59
def prefixEnd_3686301 : Nat := 4983230072969 + 3 ^ 40 * 3686301 * 2
def baseEnd_3686301 : Nat := 420632055588819347574337

theorem tailTrace_3686301 : CollatzResearch.WordTrace tailWord_3686301 prefixEnd_3686301 420632055588819347574337 := by
  unfold tailWord_3686301
  simp only [CollatzResearch.WordTrace]
  refine ⟨134450443018168521933274757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89633628678779014622183171 134450443018168521933274757)
  ·
    refine ⟨25209458065906597862489017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134450443018168521933274757 25209458065906597862489017)
    ·
      refine ⟨18907093549429948396866763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25209458065906597862489017 18907093549429948396866763)
      ·
        refine ⟨28360640324144922595300145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18907093549429948396866763 28360640324144922595300145)
        ·
          refine ⟨21270480243108691946475109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28360640324144922595300145 21270480243108691946475109)
          ·
            refine ⟨3988215045582879739964083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21270480243108691946475109 3988215045582879739964083)
            ·
              refine ⟨5982322568374319609946125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3988215045582879739964083 5982322568374319609946125)
              ·
                refine ⟨2243370963140369853729797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5982322568374319609946125 2243370963140369853729797)
                ·
                  refine ⟨420632055588819347574337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2243370963140369853729797 420632055588819347574337)
                  ·
                    rfl

theorem cell22_3686301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 3, 4].length) (baseStart_3686301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686301 prefixEnd_3686301 := by exact prefixLift 3686301
  have htrace : WordTrace (prefixWord ++ tailWord_3686301) baseStart_3686301 baseEnd_3686301 := by
    simpa [prefixWord, tailWord_3686301, baseEnd_3686301] using wordTrace_append hprefix tailTrace_3686301
  have hstable : (prefixWord ++ tailWord_3686301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686301).length < 2 ^ (prefixWord ++ tailWord_3686301).sum := by decide
  have hdescent : baseEnd_3686301 < baseStart_3686301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686333 : List Nat := [1, 4, 1, 2, 3, 3, 2, 1, 2, 3]
def baseStart_3686333 : Nat := 118140960795 + 3686333 * 2 ^ 59
def prefixEnd_3686333 : Nat := 4983230072969 + 3 ^ 40 * 3686333 * 2
def baseEnd_3686333 : Nat := 1261907121020420625922913

theorem tailTrace_3686333 : CollatzResearch.WordTrace tailWord_3686333 prefixEnd_3686333 1261907121020420625922913 := by
  unfold tailWord_3686333
  simp only [CollatzResearch.WordTrace]
  refine ⟨134451610154052591398439653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89634406769368394265626435 134451610154052591398439653)
  ·
    refine ⟨25209676903884860887207435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134451610154052591398439653 25209676903884860887207435)
    ·
      refine ⟨37814515355827291330811153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25209676903884860887207435 37814515355827291330811153)
      ·
        refine ⟨28360886516870468498108365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37814515355827291330811153 28360886516870468498108365)
        ·
          refine ⟨10635332443826425686790637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28360886516870468498108365 10635332443826425686790637)
          ·
            refine ⟨3988249666434909632546489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10635332443826425686790637 3988249666434909632546489)
            ·
              refine ⟨2991187249826182224409867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3988249666434909632546489 2991187249826182224409867)
              ·
                refine ⟨4486780874739273336614801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2991187249826182224409867 4486780874739273336614801)
                ·
                  refine ⟨3365085656054455002461101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4486780874739273336614801 3365085656054455002461101)
                  ·
                    refine ⟨1261907121020420625922913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3365085656054455002461101 1261907121020420625922913)
                    ·
                      rfl

theorem cell22_3686333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 2, 3].length) (baseStart_3686333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686333 prefixEnd_3686333 := by exact prefixLift 3686333
  have htrace : WordTrace (prefixWord ++ tailWord_3686333) baseStart_3686333 baseEnd_3686333 := by
    simpa [prefixWord, tailWord_3686333, baseEnd_3686333] using wordTrace_append hprefix tailTrace_3686333
  have hstable : (prefixWord ++ tailWord_3686333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686333).length < 2 ^ (prefixWord ++ tailWord_3686333).sum := by decide
  have hdescent : baseEnd_3686333 < baseStart_3686333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686372 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_3686372 : Nat := 118140960795 + 3686372 * 2 ^ 59
def prefixEnd_3686372 : Nat := 4983230072969 + 3 ^ 40 * 3686372 * 2
def baseEnd_3686372 : Nat := 1261920471517437524197793

theorem tailTrace_3686372 : CollatzResearch.WordTrace tailWord_3686372 prefixEnd_3686372 1261920471517437524197793 := by
  unfold tailWord_3686372
  simp only [CollatzResearch.WordTrace]
  refine ⟨67226516300455650529554685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89635355067274200706072913 67226516300455650529554685)
  ·
    refine ⟨25209943612670868948583007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67226516300455650529554685 25209943612670868948583007)
    ·
      refine ⟨37814915419006303422874511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25209943612670868948583007 37814915419006303422874511)
      ·
        refine ⟨56722373128509455134311767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37814915419006303422874511 56722373128509455134311767)
        ·
          refine ⟨85083559692764182701467651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56722373128509455134311767 85083559692764182701467651)
          ·
            refine ⟨127625339539146274052201477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85083559692764182701467651 127625339539146274052201477)
            ·
              refine ⟨23929751163589926384787777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127625339539146274052201477 23929751163589926384787777)
              ·
                refine ⟨17947313372692444788590833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23929751163589926384787777 17947313372692444788590833)
                ·
                  refine ⟨13460485029519333591443125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17947313372692444788590833 13460485029519333591443125)
                  ·
                    refine ⟨1261920471517437524197793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13460485029519333591443125 1261920471517437524197793)
                    ·
                      rfl

theorem cell22_3686372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_3686372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686372 prefixEnd_3686372 := by exact prefixLift 3686372
  have htrace : WordTrace (prefixWord ++ tailWord_3686372) baseStart_3686372 baseEnd_3686372 := by
    simpa [prefixWord, tailWord_3686372, baseEnd_3686372] using wordTrace_append hprefix tailTrace_3686372
  have hstable : (prefixWord ++ tailWord_3686372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686372).length < 2 ^ (prefixWord ++ tailWord_3686372).sum := by decide
  have hdescent : baseEnd_3686372 < baseStart_3686372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686419 : List Nat := [1, 1, 1, 2, 1, 4, 3, 5, 4]
def baseStart_3686419 : Nat := 118140960795 + 3686419 * 2 ^ 59
def prefixEnd_3686419 : Nat := 4983230072969 + 3 ^ 40 * 3686419 * 2
def baseEnd_3686419 : Nat := 420645520192648356090883

theorem tailTrace_3686419 : CollatzResearch.WordTrace tailWord_3686419 prefixEnd_3686419 420645520192648356090883 := by
  unfold tailWord_3686419
  simp only [CollatzResearch.WordTrace]
  refine ⟨134454746831741028086070311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89636497887827352057380207 134454746831741028086070311)
  ·
    refine ⟨201682120247611542129105467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134454746831741028086070311 201682120247611542129105467)
    ·
      refine ⟨302523180371417313193658201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201682120247611542129105467 302523180371417313193658201)
      ·
        refine ⟨226892385278562984895243651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302523180371417313193658201 226892385278562984895243651)
        ·
          refine ⟨340338577917844477342865477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226892385278562984895243651 340338577917844477342865477)
          ·
            refine ⟨63813483359595839501787277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340338577917844477342865477 63813483359595839501787277)
            ·
              refine ⟨23930056259848439813170229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63813483359595839501787277 23930056259848439813170229)
              ·
                refine ⟨2243442774360791232484709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23930056259848439813170229 2243442774360791232484709)
                ·
                  refine ⟨420645520192648356090883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2243442774360791232484709 420645520192648356090883)
                  ·
                    rfl

theorem cell22_3686419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 4].length) (baseStart_3686419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686419 prefixEnd_3686419 := by exact prefixLift 3686419
  have htrace : WordTrace (prefixWord ++ tailWord_3686419) baseStart_3686419 baseEnd_3686419 := by
    simpa [prefixWord, tailWord_3686419, baseEnd_3686419] using wordTrace_append hprefix tailTrace_3686419
  have hstable : (prefixWord ++ tailWord_3686419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686419).length < 2 ^ (prefixWord ++ tailWord_3686419).sum := by decide
  have hdescent : baseEnd_3686419 < baseStart_3686419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686421 : List Nat := [1, 3, 2, 1, 5, 1, 1, 3, 1, 4]
def baseStart_3686421 : Nat := 118140960795 + 3686421 * 2 ^ 59
def prefixEnd_3686421 : Nat := 4983230072969 + 3 ^ 40 * 3686421 * 2
def baseEnd_3686421 : Nat := 1261937245218817729722643

theorem tailTrace_3686421 : CollatzResearch.WordTrace tailWord_3686421 prefixEnd_3686421 1261937245218817729722643 := by
  unfold tailWord_3686421
  simp only [CollatzResearch.WordTrace]
  refine ⟨134454819777733782427643117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89636546518489188285095411 134454819777733782427643117)
  ·
    refine ⟨50420557416650168410366169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134454819777733782427643117 50420557416650168410366169)
    ·
      refine ⟨37815418062487626307774627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50420557416650168410366169 37815418062487626307774627)
      ·
        refine ⟨56723127093731439461661941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37815418062487626307774627 56723127093731439461661941)
        ·
          refine ⟨5317793165037322449530807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56723127093731439461661941 5317793165037322449530807)
          ·
            refine ⟨7976689747555983674296211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5317793165037322449530807 7976689747555983674296211)
            ·
              refine ⟨11965034621333975511444317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7976689747555983674296211 11965034621333975511444317)
              ·
                refine ⟨4486887983000240816791619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11965034621333975511444317 4486887983000240816791619)
                ·
                  refine ⟨6730331974500361225187429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4486887983000240816791619 6730331974500361225187429)
                  ·
                    refine ⟨1261937245218817729722643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6730331974500361225187429 1261937245218817729722643)
                    ·
                      rfl

theorem cell22_3686421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_3686421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686421 prefixEnd_3686421 := by exact prefixLift 3686421
  have htrace : WordTrace (prefixWord ++ tailWord_3686421) baseStart_3686421 baseEnd_3686421 := by
    simpa [prefixWord, tailWord_3686421, baseEnd_3686421] using wordTrace_append hprefix tailTrace_3686421
  have hstable : (prefixWord ++ tailWord_3686421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686421).length < 2 ^ (prefixWord ++ tailWord_3686421).sum := by decide
  have hdescent : baseEnd_3686421 < baseStart_3686421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686436 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 6]
def baseStart_3686436 : Nat := 118140960795 + 3686436 * 2 ^ 59
def prefixEnd_3686436 : Nat := 4983230072969 + 3 ^ 40 * 3686436 * 2
def baseEnd_3686436 : Nat := 420647460008454230199199

theorem tailTrace_3686436 : CollatzResearch.WordTrace tailWord_3686436 prefixEnd_3686436 420647460008454230199199 := by
  unfold tailWord_3686436
  simp only [CollatzResearch.WordTrace]
  refine ⟨67227683436339719994719581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89636911248452959992959441 67227683436339719994719581)
  ·
    refine ⟨25210381288627394998019843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67227683436339719994719581 25210381288627394998019843)
    ·
      refine ⟨37815571932941092497029765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25210381288627394998019843 37815571932941092497029765)
      ·
        refine ⟨7090419737426454843193081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37815571932941092497029765 7090419737426454843193081)
        ·
          refine ⟨5317814803069841132394811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7090419737426454843193081 5317814803069841132394811)
          ·
            refine ⟨7976722204604761698592217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5317814803069841132394811 7976722204604761698592217)
            ·
              refine ⟨5982541653453571273944163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7976722204604761698592217 5982541653453571273944163)
              ·
                refine ⟨8973812480180356910916245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5982541653453571273944163 8973812480180356910916245)
                ·
                  refine ⟨420647460008454230199199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8973812480180356910916245 420647460008454230199199)
                  ·
                    rfl

theorem cell22_3686436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_3686436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686436 prefixEnd_3686436 := by exact prefixLift 3686436
  have htrace : WordTrace (prefixWord ++ tailWord_3686436) baseStart_3686436 baseEnd_3686436 := by
    simpa [prefixWord, tailWord_3686436, baseEnd_3686436] using wordTrace_append hprefix tailTrace_3686436
  have hstable : (prefixWord ++ tailWord_3686436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686436).length < 2 ^ (prefixWord ++ tailWord_3686436).sum := by decide
  have hdescent : baseEnd_3686436 < baseStart_3686436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686464 : List Nat := [2, 1, 1, 2, 2, 4, 4, 6]
def baseStart_3686464 : Nat := 118140960795 + 3686464 * 2 ^ 59
def prefixEnd_3686464 : Nat := 4983230072969 + 3 ^ 40 * 3686464 * 2
def baseEnd_3686464 : Nat := 140216884999731105655279

theorem tailTrace_3686464 : CollatzResearch.WordTrace tailWord_3686464 prefixEnd_3686464 140216884999731105655279 := by
  unfold tailWord_3686464
  simp only [CollatzResearch.WordTrace]
  refine ⟨67228194058289000385729223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89637592077718667180972297 67228194058289000385729223)
  ·
    refine ⟨100842291087433500578593835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67228194058289000385729223 100842291087433500578593835)
    ·
      refine ⟨151263436631150250867890753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100842291087433500578593835 151263436631150250867890753)
      ·
        refine ⟨113447577473362688150918065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151263436631150250867890753 113447577473362688150918065)
        ·
          refine ⟨85085683105022016113188549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113447577473362688150918065 85085683105022016113188549)
          ·
            refine ⟨15953565582191628021222853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85085683105022016113188549 15953565582191628021222853)
            ·
              refine ⟨2991293546660930253979285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15953565582191628021222853 2991293546660930253979285)
              ·
                refine ⟨140216884999731105655279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2991293546660930253979285 140216884999731105655279)
                ·
                  rfl

theorem cell22_3686464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 6].length) (baseStart_3686464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686464 prefixEnd_3686464 := by exact prefixLift 3686464
  have htrace : WordTrace (prefixWord ++ tailWord_3686464) baseStart_3686464 baseEnd_3686464 := by
    simpa [prefixWord, tailWord_3686464, baseEnd_3686464] using wordTrace_append hprefix tailTrace_3686464
  have hstable : (prefixWord ++ tailWord_3686464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686464).length < 2 ^ (prefixWord ++ tailWord_3686464).sum := by decide
  have hdescent : baseEnd_3686464 < baseStart_3686464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686496 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 3, 3]
def baseStart_3686496 : Nat := 118140960795 + 3686496 * 2 ^ 59
def prefixEnd_3686496 : Nat := 4983230072969 + 3 ^ 40 * 3686496 * 2
def baseEnd_3686496 : Nat := 1261962919251542534097413

theorem tailTrace_3686496 : CollatzResearch.WordTrace tailWord_3686496 prefixEnd_3686496 1261962919251542534097413 := by
  unfold tailWord_3686496
  simp only [CollatzResearch.WordTrace]
  refine ⟨67228777626231035118311671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89638370168308046824415561 67228777626231035118311671)
  ·
    refine ⟨100843166439346552677467507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67228777626231035118311671 100843166439346552677467507)
    ·
      refine ⟨151264749659019829016201261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100843166439346552677467507 151264749659019829016201261)
      ·
        refine ⟨56724281122132435881075473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151264749659019829016201261 56724281122132435881075473)
        ·
          refine ⟨42543210841599326910806605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56724281122132435881075473 42543210841599326910806605)
          ·
            refine ⟨15953704065599747591552477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42543210841599326910806605 15953704065599747591552477)
            ·
              refine ⟨5982639024599905346832179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15953704065599747591552477 5982639024599905346832179)
              ·
                refine ⟨8973958536899858020248269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5982639024599905346832179 8973958536899858020248269)
                ·
                  refine ⟨3365234451337446757593101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8973958536899858020248269 3365234451337446757593101)
                  ·
                    refine ⟨1261962919251542534097413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3365234451337446757593101 1261962919251542534097413)
                    ·
                      rfl

theorem cell22_3686496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 3, 3].length) (baseStart_3686496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686496 prefixEnd_3686496 := by exact prefixLift 3686496
  have htrace : WordTrace (prefixWord ++ tailWord_3686496) baseStart_3686496 baseEnd_3686496 := by
    simpa [prefixWord, tailWord_3686496, baseEnd_3686496] using wordTrace_append hprefix tailTrace_3686496
  have hstable : (prefixWord ++ tailWord_3686496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686496).length < 2 ^ (prefixWord ++ tailWord_3686496).sum := by decide
  have hdescent : baseEnd_3686496 < baseStart_3686496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686558 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 2, 5]
def baseStart_3686558 : Nat := 118140960795 + 3686558 * 2 ^ 59
def prefixEnd_3686558 : Nat := 4983230072969 + 3 ^ 40 * 3686558 * 2
def baseEnd_3686558 : Nat := 1261984143118595039047223

theorem tailTrace_3686558 : CollatzResearch.WordTrace tailWord_3686558 prefixEnd_3686558 1261984143118595039047223 := by
  unfold tailWord_3686558
  simp only [CollatzResearch.WordTrace]
  refine ⟨16807477072279681853172541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89639877718824969883586885 16807477072279681853172541)
  ·
    refine ⟨6302803902104880694939703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16807477072279681853172541 6302803902104880694939703)
    ·
      refine ⟨9454205853157321042409555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6302803902104880694939703 9454205853157321042409555)
      ·
        refine ⟨14181308779735981563614333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9454205853157321042409555 14181308779735981563614333)
        ·
          refine ⟨5317990792400993086355375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14181308779735981563614333 5317990792400993086355375)
          ·
            refine ⟨7976986188601489629533063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5317990792400993086355375 7976986188601489629533063)
            ·
              refine ⟨11965479282902234444299595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7976986188601489629533063 11965479282902234444299595)
              ·
                refine ⟨17948218924353351666449393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11965479282902234444299595 17948218924353351666449393)
                ·
                  refine ⟨13461164193265013749837045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17948218924353351666449393 13461164193265013749837045)
                  ·
                    refine ⟨1261984143118595039047223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13461164193265013749837045 1261984143118595039047223)
                    ·
                      rfl

theorem cell22_3686558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_3686558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686558 prefixEnd_3686558 := by exact prefixLift 3686558
  have htrace : WordTrace (prefixWord ++ tailWord_3686558) baseStart_3686558 baseEnd_3686558 := by
    simpa [prefixWord, tailWord_3686558, baseEnd_3686558] using wordTrace_append hprefix tailTrace_3686558
  have hstable : (prefixWord ++ tailWord_3686558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686558).length < 2 ^ (prefixWord ++ tailWord_3686558).sum := by decide
  have hdescent : baseEnd_3686558 < baseStart_3686558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686584 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 1, 6]
def baseStart_3686584 : Nat := 118140960795 + 3686584 * 2 ^ 59
def prefixEnd_3686584 : Nat := 4983230072969 + 3 ^ 40 * 3686584 * 2
def baseEnd_3686584 : Nat := 1261993043449939637897143

theorem tailTrace_3686584 : CollatzResearch.WordTrace tailWord_3686584 prefixEnd_3686584 1261993043449939637897143 := by
  unfold tailWord_3686584
  simp only [CollatzResearch.WordTrace]
  refine ⟨67230382438071630632913403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89640509917428840843884537 67230382438071630632913403)
  ·
    refine ⟨100845573657107445949370105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67230382438071630632913403 100845573657107445949370105)
    ·
      refine ⟨75634180242830584462027579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100845573657107445949370105 75634180242830584462027579)
      ·
        refine ⟨113451270364245876693041369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75634180242830584462027579 113451270364245876693041369)
        ·
          refine ⟨85088452773184407519781027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113451270364245876693041369 85088452773184407519781027)
          ·
            refine ⟨127632679159776611279671541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85088452773184407519781027 127632679159776611279671541)
            ·
              refine ⟨11965563671229057307469207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127632679159776611279671541 11965563671229057307469207)
              ·
                refine ⟨17948345506843585961203811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11965563671229057307469207 17948345506843585961203811)
                ·
                  refine ⟨26922518260265378941805717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17948345506843585961203811 26922518260265378941805717)
                  ·
                    refine ⟨1261993043449939637897143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26922518260265378941805717 1261993043449939637897143)
                    ·
                      rfl

theorem cell22_3686584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_3686584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686584 prefixEnd_3686584 := by exact prefixLift 3686584
  have htrace : WordTrace (prefixWord ++ tailWord_3686584) baseStart_3686584 baseEnd_3686584 := by
    simpa [prefixWord, tailWord_3686584, baseEnd_3686584] using wordTrace_append hprefix tailTrace_3686584
  have hstable : (prefixWord ++ tailWord_3686584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686584).length < 2 ^ (prefixWord ++ tailWord_3686584).sum := by decide
  have hdescent : baseEnd_3686584 < baseStart_3686584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686691 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 3, 4]
def baseStart_3686691 : Nat := 118140960795 + 3686691 * 2 ^ 59
def prefixEnd_3686691 : Nat := 4983230072969 + 3 ^ 40 * 3686691 * 2
def baseEnd_3686691 : Nat := 1262029671736627025471815

theorem tailTrace_3686691 : CollatzResearch.WordTrace tailWord_3686691 prefixEnd_3686691 1262029671736627025471815 := by
  unfold tailWord_3686691
  simp only [CollatzResearch.WordTrace]
  refine ⟨134464667486755618539971927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89643111657837079026647951 134464667486755618539971927)
  ·
    refine ⟨201697001230133427809957891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134464667486755618539971927 201697001230133427809957891)
    ·
      refine ⟨302545501845200141714936837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201697001230133427809957891 302545501845200141714936837)
      ·
        refine ⟨56727281595975026571550657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302545501845200141714936837 56727281595975026571550657)
        ·
          refine ⟨42545461196981269928662993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56727281595975026571550657 42545461196981269928662993)
          ·
            refine ⟨31909095897735952446497245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42545461196981269928662993 31909095897735952446497245)
            ·
              refine ⟨11965910961650982167436467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31909095897735952446497245 11965910961650982167436467)
              ·
                refine ⟨17948866442476473251154701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11965910961650982167436467 17948866442476473251154701)
                ·
                  refine ⟨6730824915928677469183013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17948866442476473251154701 6730824915928677469183013)
                  ·
                    refine ⟨1262029671736627025471815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6730824915928677469183013 1262029671736627025471815)
                    ·
                      rfl

theorem cell22_3686691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 4].length) (baseStart_3686691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686691 prefixEnd_3686691 := by exact prefixLift 3686691
  have htrace : WordTrace (prefixWord ++ tailWord_3686691) baseStart_3686691 baseEnd_3686691 := by
    simpa [prefixWord, tailWord_3686691, baseEnd_3686691] using wordTrace_append hprefix tailTrace_3686691
  have hstable : (prefixWord ++ tailWord_3686691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686691).length < 2 ^ (prefixWord ++ tailWord_3686691).sum := by decide
  have hdescent : baseEnd_3686691 < baseStart_3686691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686860 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 3, 4]
def baseStart_3686860 : Nat := 118140960795 + 3686860 * 2 ^ 59
def prefixEnd_3686860 : Nat := 4983230072969 + 3 ^ 40 * 3686860 * 2
def baseEnd_3686860 : Nat := 1262087523890366917996297

theorem tailTrace_3686860 : CollatzResearch.WordTrace tailWord_3686860 prefixEnd_3686860 1262087523890366917996297 := by
  unfold tailWord_3686860
  simp only [CollatzResearch.WordTrace]
  refine ⟨67235415711571680201437017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89647220948762240268582689 67235415711571680201437017)
  ·
    refine ⟨50426561783678760151077763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67235415711571680201437017 50426561783678760151077763)
    ·
      refine ⟨75639842675518140226616645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50426561783678760151077763 75639842675518140226616645)
      ·
        refine ⟨14182470501659651292490621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75639842675518140226616645 14182470501659651292490621)
        ·
          refine ⟨5318426438122369234683983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14182470501659651292490621 5318426438122369234683983)
          ·
            refine ⟨7977639657183553852025975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5318426438122369234683983 7977639657183553852025975)
            ·
              refine ⟨11966459485775330778038963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7977639657183553852025975 11966459485775330778038963)
              ·
                refine ⟨17949689228662996167058445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11966459485775330778038963 17949689228662996167058445)
                ·
                  refine ⟨6731133460748623562646917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17949689228662996167058445 6731133460748623562646917)
                  ·
                    refine ⟨1262087523890366917996297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6731133460748623562646917 1262087523890366917996297)
                    ·
                      rfl

theorem cell22_3686860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_3686860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686860 prefixEnd_3686860 := by exact prefixLift 3686860
  have htrace : WordTrace (prefixWord ++ tailWord_3686860) baseStart_3686860 baseEnd_3686860 := by
    simpa [prefixWord, tailWord_3686860, baseEnd_3686860] using wordTrace_append hprefix tailTrace_3686860
  have hstable : (prefixWord ++ tailWord_3686860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686860).length < 2 ^ (prefixWord ++ tailWord_3686860).sum := by decide
  have hdescent : baseEnd_3686860 < baseStart_3686860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686873 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 1, 5]
def baseStart_3686873 : Nat := 118140960795 + 3686873 * 2 ^ 59
def prefixEnd_3686873 : Nat := 4983230072969 + 3 ^ 40 * 3686873 * 2
def baseEnd_3686873 : Nat := 1262091974056039217421257

theorem tailTrace_3686873 : CollatzResearch.WordTrace tailWord_3686873 prefixEnd_3686873 1262091974056039217421257 := by
  unfold tailWord_3686873
  simp only [CollatzResearch.WordTrace]
  refine ⟨134471305572096263623097273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89647537048064175748731515 134471305572096263623097273)
  ·
    refine ⟨100853479179072197717322955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134471305572096263623097273 100853479179072197717322955)
    ·
      refine ⟨151280218768608296575984433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100853479179072197717322955 151280218768608296575984433)
      ·
        refine ⟨113460164076456222431988325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151280218768608296575984433 113460164076456222431988325)
        ·
          refine ⟨21273780764335541705997811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113460164076456222431988325 21273780764335541705997811)
          ·
            refine ⟨31910671146503312558996717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21273780764335541705997811 31910671146503312558996717)
            ·
              refine ⟨11966501679938742209623769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31910671146503312558996717 11966501679938742209623769)
              ·
                refine ⟨8974876259954056657217827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11966501679938742209623769 8974876259954056657217827)
                ·
                  refine ⟨13462314389931084985826741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8974876259954056657217827 13462314389931084985826741)
                  ·
                    refine ⟨1262091974056039217421257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13462314389931084985826741 1262091974056039217421257)
                    ·
                      rfl

theorem cell22_3686873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_3686873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686873 prefixEnd_3686873 := by exact prefixLift 3686873
  have htrace : WordTrace (prefixWord ++ tailWord_3686873) baseStart_3686873 baseEnd_3686873 := by
    simpa [prefixWord, tailWord_3686873, baseEnd_3686873] using wordTrace_append hprefix tailTrace_3686873
  have hstable : (prefixWord ++ tailWord_3686873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686873).length < 2 ^ (prefixWord ++ tailWord_3686873).sum := by decide
  have hdescent : baseEnd_3686873 < baseStart_3686873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686877 : List Nat := [1, 4, 3, 1, 1, 1, 5, 1, 1, 4]
def baseStart_3686877 : Nat := 118140960795 + 3686877 * 2 ^ 59
def prefixEnd_3686877 : Nat := 4983230072969 + 3 ^ 40 * 3686877 * 2
def baseEnd_3686877 : Nat := 1262093343337784540321245

theorem tailTrace_3686877 : CollatzResearch.WordTrace tailWord_3686877 prefixEnd_3686877 1262093343337784540321245 := by
  unfold tailWord_3686877
  simp only [CollatzResearch.WordTrace]
  refine ⟨134471451464081772306242885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89647634309387848204161923 134471451464081772306242885)
  ·
    refine ⟨25213397149515332307420541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134471451464081772306242885 25213397149515332307420541)
    ·
      refine ⟨9455023931068249615282703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25213397149515332307420541 9455023931068249615282703)
      ·
        refine ⟨14182535896602374422924055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9455023931068249615282703 14182535896602374422924055)
        ·
          refine ⟨21273803844903561634386083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14182535896602374422924055 21273803844903561634386083)
          ·
            refine ⟨31910705767355342451579125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21273803844903561634386083 31910705767355342451579125)
            ·
              refine ⟨2991628665689563354835543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31910705767355342451579125 2991628665689563354835543)
              ·
                refine ⟨4487442998534345032253315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2991628665689563354835543 4487442998534345032253315)
                ·
                  refine ⟨6731164497801517548379973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4487442998534345032253315 6731164497801517548379973)
                  ·
                    refine ⟨1262093343337784540321245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6731164497801517548379973 1262093343337784540321245)
                    ·
                      rfl

theorem cell22_3686877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_3686877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686877 prefixEnd_3686877 := by exact prefixLift 3686877
  have htrace : WordTrace (prefixWord ++ tailWord_3686877) baseStart_3686877 baseEnd_3686877 := by
    simpa [prefixWord, tailWord_3686877, baseEnd_3686877] using wordTrace_append hprefix tailTrace_3686877
  have hstable : (prefixWord ++ tailWord_3686877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686877).length < 2 ^ (prefixWord ++ tailWord_3686877).sum := by decide
  have hdescent : baseEnd_3686877 < baseStart_3686877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686952 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 3, 3]
def baseStart_3686952 : Nat := 118140960795 + 3686952 * 2 ^ 59
def prefixEnd_3686952 : Nat := 4983230072969 + 3 ^ 40 * 3686952 * 2
def baseEnd_3686952 : Nat := 1262119017370509344696015

theorem tailTrace_3686952 : CollatzResearch.WordTrace tailWord_3686952 prefixEnd_3686952 1262119017370509344696015 := by
  unfold tailWord_3686952
  simp only [CollatzResearch.WordTrace]
  refine ⟨67237093469405030057611555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89649457959206706743482073 67237093469405030057611555)
  ·
    refine ⟨100855640204107545086417333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67237093469405030057611555 100855640204107545086417333)
    ·
      refine ⟨9455216269135082351851625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100855640204107545086417333 9455216269135082351851625)
      ·
        refine ⟨7091412201851311763888719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9455216269135082351851625 7091412201851311763888719)
        ·
          refine ⟨10637118302776967645833079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7091412201851311763888719 10637118302776967645833079)
          ·
            refine ⟨15955677454165451468749619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10637118302776967645833079 15955677454165451468749619)
            ·
              refine ⟨23933516181248177203124429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15955677454165451468749619 23933516181248177203124429)
              ·
                refine ⟨8975068567968066451171661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23933516181248177203124429 8975068567968066451171661)
                ·
                  refine ⟨3365650712988024919189373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8975068567968066451171661 3365650712988024919189373)
                  ·
                    refine ⟨1262119017370509344696015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3365650712988024919189373 1262119017370509344696015)
                    ·
                      rfl

theorem cell22_3686952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_3686952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686952 prefixEnd_3686952 := by exact prefixLift 3686952
  have htrace : WordTrace (prefixWord ++ tailWord_3686952) baseStart_3686952 baseEnd_3686952 := by
    simpa [prefixWord, tailWord_3686952, baseEnd_3686952] using wordTrace_append hprefix tailTrace_3686952
  have hstable : (prefixWord ++ tailWord_3686952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686952).length < 2 ^ (prefixWord ++ tailWord_3686952).sum := by decide
  have hdescent : baseEnd_3686952 < baseStart_3686952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686963 : List Nat := [1, 1, 1, 2, 4, 2, 1, 3, 2, 5]
def baseStart_3686963 : Nat := 118140960795 + 3686963 * 2 ^ 59
def prefixEnd_3686963 : Nat := 4983230072969 + 3 ^ 40 * 3686963 * 2
def baseEnd_3686963 : Nat := 1262122782895308982670981

theorem tailTrace_3686963 : CollatzResearch.WordTrace tailWord_3686963 prefixEnd_3686963 1262122782895308982670981 := by
  unfold tailWord_3686963
  simp only [CollatzResearch.WordTrace]
  refine ⟨134474588141770208993873543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89649725427846805995915695 134474588141770208993873543)
  ·
    refine ⟨201711882212655313490810315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134474588141770208993873543 201711882212655313490810315)
    ·
      refine ⟨302567823318982970236215473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201711882212655313490810315 302567823318982970236215473)
      ·
        refine ⟨226925867489237227677161605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302567823318982970236215473 226925867489237227677161605)
        ·
          refine ⟨42548600154231980189467801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 226925867489237227677161605 42548600154231980189467801)
          ·
            refine ⟨31911450115673985142100851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42548600154231980189467801 31911450115673985142100851)
            ·
              refine ⟨47867175173510977713151277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31911450115673985142100851 47867175173510977713151277)
              ·
                refine ⟨17950190690066616642431729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47867175173510977713151277 17950190690066616642431729)
                ·
                  refine ⟨13462643017549962481823797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17950190690066616642431729 13462643017549962481823797)
                  ·
                    refine ⟨1262122782895308982670981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13462643017549962481823797 1262122782895308982670981)
                    ·
                      rfl

theorem cell22_3686963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 5].length) (baseStart_3686963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686963 prefixEnd_3686963 := by exact prefixLift 3686963
  have htrace : WordTrace (prefixWord ++ tailWord_3686963) baseStart_3686963 baseEnd_3686963 := by
    simpa [prefixWord, tailWord_3686963, baseEnd_3686963] using wordTrace_append hprefix tailTrace_3686963
  have hstable : (prefixWord ++ tailWord_3686963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686963).length < 2 ^ (prefixWord ++ tailWord_3686963).sum := by decide
  have hdescent : baseEnd_3686963 < baseStart_3686963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3686982 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 7]
def baseStart_3686982 : Nat := 118140960795 + 3686982 * 2 ^ 59
def prefixEnd_3686982 : Nat := 4983230072969 + 3 ^ 40 * 3686982 * 2
def baseEnd_3686982 : Nat := 420709762327866422148641

theorem tailTrace_3686982 : CollatzResearch.WordTrace tailWord_3686982 prefixEnd_3686982 420709762327866422148641 := by
  unfold tailWord_3686982
  simp only [CollatzResearch.WordTrace]
  refine ⟨4202352535271917976212975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89650187419134250159210133 4202352535271917976212975)
  ·
    refine ⟨6303528802907876964319463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4202352535271917976212975 6303528802907876964319463)
    ·
      refine ⟨9455293204361815446479195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6303528802907876964319463 9455293204361815446479195)
      ·
        refine ⟨14182939806542723169718793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9455293204361815446479195 14182939806542723169718793)
        ·
          refine ⟨10637204854907042377289095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14182939806542723169718793 10637204854907042377289095)
          ·
            refine ⟨15955807282360563565933643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10637204854907042377289095 15955807282360563565933643)
            ·
              refine ⟨23933710923540845348900465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15955807282360563565933643 23933710923540845348900465)
              ·
                refine ⟨17950283192655634011675349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23933710923540845348900465 17950283192655634011675349)
                ·
                  refine ⟨420709762327866422148641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17950283192655634011675349 420709762327866422148641)
                  ·
                    rfl

theorem cell22_3686982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_3686982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3686982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3686982 prefixEnd_3686982 := by exact prefixLift 3686982
  have htrace : WordTrace (prefixWord ++ tailWord_3686982) baseStart_3686982 baseEnd_3686982 := by
    simpa [prefixWord, tailWord_3686982, baseEnd_3686982] using wordTrace_append hprefix tailTrace_3686982
  have hstable : (prefixWord ++ tailWord_3686982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3686982).length < 2 ^ (prefixWord ++ tailWord_3686982).sum := by decide
  have hdescent : baseEnd_3686982 < baseStart_3686982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3686982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687016 : List Nat := [2, 1, 4, 3, 3, 1, 2, 1, 5]
def baseStart_3687016 : Nat := 118140960795 + 3687016 * 2 ^ 59
def prefixEnd_3687016 : Nat := 4983230072969 + 3 ^ 40 * 3687016 * 2
def baseEnd_3687016 : Nat := 420713641959478170365273

theorem tailTrace_3687016 : CollatzResearch.WordTrace tailWord_3687016 prefixEnd_3687016 420713641959478170365273 := by
  unfold tailWord_3687016
  simp only [CollatzResearch.WordTrace]
  refine ⟨67238260605289099522776451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89651014140385466030368601 67238260605289099522776451)
  ·
    refine ⟨100857390907933649284164677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67238260605289099522776451 100857390907933649284164677)
    ·
      refine ⟨18910760795237559240780877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100857390907933649284164677 18910760795237559240780877)
      ·
        refine ⟨7091535298214084715292829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18910760795237559240780877 7091535298214084715292829)
        ·
          refine ⟨2659325736830281768234811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7091535298214084715292829 2659325736830281768234811)
          ·
            refine ⟨3988988605245422652352217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2659325736830281768234811 3988988605245422652352217)
            ·
              refine ⟨2991741453934066989264163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3988988605245422652352217 2991741453934066989264163)
              ·
                refine ⟨4487612180901100483896245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2991741453934066989264163 4487612180901100483896245)
                ·
                  refine ⟨420713641959478170365273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4487612180901100483896245 420713641959478170365273)
                  ·
                    rfl

theorem cell22_3687016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 5].length) (baseStart_3687016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687016 prefixEnd_3687016 := by exact prefixLift 3687016
  have htrace : WordTrace (prefixWord ++ tailWord_3687016) baseStart_3687016 baseEnd_3687016 := by
    simpa [prefixWord, tailWord_3687016, baseEnd_3687016] using wordTrace_append hprefix tailTrace_3687016
  have hstable : (prefixWord ++ tailWord_3687016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687016).length < 2 ^ (prefixWord ++ tailWord_3687016).sum := by decide
  have hdescent : baseEnd_3687016 < baseStart_3687016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687023 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 3, 6]
def baseStart_3687023 : Nat := 118140960795 + 3687023 * 2 ^ 59
def prefixEnd_3687023 : Nat := 4983230072969 + 3 ^ 40 * 3687023 * 2
def baseEnd_3687023 : Nat := 1262143322121488826170797

theorem tailTrace_3687023 : CollatzResearch.WordTrace tailWord_3687023 prefixEnd_3687023 1262143322121488826170797 := by
  unfold tailWord_3687023
  simp only [CollatzResearch.WordTrace]
  refine ⟨134476776521552839241057723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89651184347701892827371815 134476776521552839241057723)
  ·
    refine ⟨201715164782329258861586585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134476776521552839241057723 201715164782329258861586585)
    ·
      refine ⟨151286373586746944146189939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201715164782329258861586585 151286373586746944146189939)
      ·
        refine ⟨226929560380120416219284909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151286373586746944146189939 226929560380120416219284909)
        ·
          refine ⟨85098585142545156082231841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226929560380120416219284909 85098585142545156082231841)
          ·
            refine ⟨63823938856908867061673881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85098585142545156082231841 63823938856908867061673881)
            ·
              refine ⟨47867954142681650296255411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63823938856908867061673881 47867954142681650296255411)
              ·
                refine ⟨71801931214022475444383117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47867954142681650296255411 71801931214022475444383117)
                ·
                  refine ⟨26925724205258428291643669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71801931214022475444383117 26925724205258428291643669)
                  ·
                    refine ⟨1262143322121488826170797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26925724205258428291643669 1262143322121488826170797)
                    ·
                      rfl

theorem cell22_3687023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 6].length) (baseStart_3687023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687023 prefixEnd_3687023 := by exact prefixLift 3687023
  have htrace : WordTrace (prefixWord ++ tailWord_3687023) baseStart_3687023 baseEnd_3687023 := by
    simpa [prefixWord, tailWord_3687023, baseEnd_3687023] using wordTrace_append hprefix tailTrace_3687023
  have hstable : (prefixWord ++ tailWord_3687023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687023).length < 2 ^ (prefixWord ++ tailWord_3687023).sum := by decide
  have hdescent : baseEnd_3687023 < baseStart_3687023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687040 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 2, 4]
def baseStart_3687040 : Nat := 118140960795 + 3687040 * 2 ^ 59
def prefixEnd_3687040 : Nat := 4983230072969 + 3 ^ 40 * 3687040 * 2
def baseEnd_3687040 : Nat := 1262149141568906448495745

theorem tailTrace_3687040 : CollatzResearch.WordTrace tailWord_3687040 prefixEnd_3687040 1262149141568906448495745 := by
  unfold tailWord_3687040
  simp only [CollatzResearch.WordTrace]
  refine ⟨67238698281245625572213287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89651597708327500762951049 67238698281245625572213287)
  ·
    refine ⟨100858047421868438358319931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67238698281245625572213287 100858047421868438358319931)
    ·
      refine ⟨151287071132802657537479897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100858047421868438358319931 151287071132802657537479897)
      ·
        refine ⟨113465303349601993153109923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151287071132802657537479897 113465303349601993153109923)
        ·
          refine ⟨170197955024402989729664885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113465303349601993153109923 170197955024402989729664885)
          ·
            refine ⟨15956058283537780287156083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170197955024402989729664885 15956058283537780287156083)
            ·
              refine ⟨23934087425306670430734125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15956058283537780287156083 23934087425306670430734125)
              ·
                refine ⟨8975282784490001411525297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23934087425306670430734125 8975282784490001411525297)
                ·
                  refine ⟨6731462088367501058643973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8975282784490001411525297 6731462088367501058643973)
                  ·
                    refine ⟨1262149141568906448495745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6731462088367501058643973 1262149141568906448495745)
                    ·
                      rfl

theorem cell22_3687040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_3687040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687040 prefixEnd_3687040 := by exact prefixLift 3687040
  have htrace : WordTrace (prefixWord ++ tailWord_3687040) baseStart_3687040 baseEnd_3687040 := by
    simpa [prefixWord, tailWord_3687040, baseEnd_3687040] using wordTrace_append hprefix tailTrace_3687040
  have hstable : (prefixWord ++ tailWord_3687040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687040).length < 2 ^ (prefixWord ++ tailWord_3687040).sum := by decide
  have hdescent : baseEnd_3687040 < baseStart_3687040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687072 : List Nat := [2, 1, 1, 4, 4, 2, 1, 7]
def baseStart_3687072 : Nat := 118140960795 + 3687072 * 2 ^ 59
def prefixEnd_3687072 : Nat := 4983230072969 + 3 ^ 40 * 3687072 * 2
def baseEnd_3687072 : Nat := 140240010646985447966183

theorem tailTrace_3687072 : CollatzResearch.WordTrace tailWord_3687072 prefixEnd_3687072 140240010646985447966183 := by
  unfold tailWord_3687072
  simp only [CollatzResearch.WordTrace]
  refine ⟨67239281849187660304795735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89652375798916880406394313 67239281849187660304795735)
  ·
    refine ⟨100858922773781490457193603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67239281849187660304795735 100858922773781490457193603)
    ·
      refine ⟨151288384160672235685790405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100858922773781490457193603 151288384160672235685790405)
      ·
        refine ⟨28366572030126044191085701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151288384160672235685790405 28366572030126044191085701)
        ·
          refine ⟨5318732255648633285828569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28366572030126044191085701 5318732255648633285828569)
          ·
            refine ⟨3989049191736474964371427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5318732255648633285828569 3989049191736474964371427)
            ·
              refine ⟨5983573787604712446557141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3989049191736474964371427 5983573787604712446557141)
              ·
                refine ⟨140240010646985447966183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5983573787604712446557141 140240010646985447966183)
                ·
                  rfl

theorem cell22_3687072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 7].length) (baseStart_3687072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687072 prefixEnd_3687072 := by exact prefixLift 3687072
  have htrace : WordTrace (prefixWord ++ tailWord_3687072) baseStart_3687072 baseEnd_3687072 := by
    simpa [prefixWord, tailWord_3687072, baseEnd_3687072] using wordTrace_append hprefix tailTrace_3687072
  have hstable : (prefixWord ++ tailWord_3687072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687072).length < 2 ^ (prefixWord ++ tailWord_3687072).sum := by decide
  have hdescent : baseEnd_3687072 < baseStart_3687072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687087 : List Nat := [1, 1, 2, 1, 2, 6, 1, 2, 3, 3]
def baseStart_3687087 : Nat := 118140960795 + 3687087 * 2 ^ 59
def prefixEnd_3687087 : Nat := 4983230072969 + 3 ^ 40 * 3687087 * 2
def baseEnd_3687087 : Nat := 1262165230629413992570601

theorem tailTrace_3687087 : CollatzResearch.WordTrace tailWord_3687087 prefixEnd_3687087 1262165230629413992570601 := by
  unfold tailWord_3687087
  simp only [CollatzResearch.WordTrace]
  refine ⟨134479110793320978171387515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89652740528880652114258343 134479110793320978171387515)
  ·
    refine ⟨201718666189981467257081273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134479110793320978171387515 201718666189981467257081273)
    ·
      refine ⟨151288999642486100442810955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201718666189981467257081273 151288999642486100442810955)
      ·
        refine ⟨226933499463729150664216433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151288999642486100442810955 226933499463729150664216433)
        ·
          refine ⟨170200124597796862998162325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 226933499463729150664216433 170200124597796862998162325)
          ·
            refine ⟨7978130840521727953038859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 170200124597796862998162325 7978130840521727953038859)
            ·
              refine ⟨11967196260782591929558289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7978130840521727953038859 11967196260782591929558289)
              ·
                refine ⟨8975397195586943947168717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11967196260782591929558289 8975397195586943947168717)
                ·
                  refine ⟨3365773948345103980188269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8975397195586943947168717 3365773948345103980188269)
                  ·
                    refine ⟨1262165230629413992570601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3365773948345103980188269 1262165230629413992570601)
                    ·
                      rfl

theorem cell22_3687087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 3].length) (baseStart_3687087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687087 prefixEnd_3687087 := by exact prefixLift 3687087
  have htrace : WordTrace (prefixWord ++ tailWord_3687087) baseStart_3687087 baseEnd_3687087 := by
    simpa [prefixWord, tailWord_3687087, baseEnd_3687087] using wordTrace_append hprefix tailTrace_3687087
  have hstable : (prefixWord ++ tailWord_3687087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687087).length < 2 ^ (prefixWord ++ tailWord_3687087).sum := by decide
  have hdescent : baseEnd_3687087 < baseStart_3687087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687089 : List Nat := [1, 2, 2, 6, 1, 1, 3, 6]
def baseStart_3687089 : Nat := 118140960795 + 3687089 * 2 ^ 59
def prefixEnd_3687089 : Nat := 4983230072969 + 3 ^ 40 * 3687089 * 2
def baseEnd_3687089 : Nat := 140240657252254072668955

theorem tailTrace_3687089 : CollatzResearch.WordTrace tailWord_3687089 prefixEnd_3687089 140240657252254072668955 := by
  unfold tailWord_3687089
  simp only [CollatzResearch.WordTrace]
  refine ⟨134479183739313732512960321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89652789159542488341973547 134479183739313732512960321)
  ·
    refine ⟨100859387804485299384720241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134479183739313732512960321 100859387804485299384720241)
    ·
      refine ⟨75644540853363974538540181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100859387804485299384720241 75644540853363974538540181)
      ·
        refine ⟨3545837852501436306494071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75644540853363974538540181 3545837852501436306494071)
        ·
          refine ⟨5318756778752154459741107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545837852501436306494071 5318756778752154459741107)
          ·
            refine ⟨7978135168128231689611661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5318756778752154459741107 7978135168128231689611661)
            ·
              refine ⟨2991800688048086883604373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7978135168128231689611661 2991800688048086883604373)
              ·
                refine ⟨140240657252254072668955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2991800688048086883604373 140240657252254072668955)
                ·
                  rfl

theorem cell22_3687089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 6].length) (baseStart_3687089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687089 prefixEnd_3687089 := by exact prefixLift 3687089
  have htrace : WordTrace (prefixWord ++ tailWord_3687089) baseStart_3687089 baseEnd_3687089 := by
    simpa [prefixWord, tailWord_3687089, baseEnd_3687089] using wordTrace_append hprefix tailTrace_3687089
  have hstable : (prefixWord ++ tailWord_3687089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687089).length < 2 ^ (prefixWord ++ tailWord_3687089).sum := by decide
  have hdescent : baseEnd_3687089 < baseStart_3687089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687100 : List Nat := [2, 2, 2, 3, 1, 1, 2, 2, 7]
def baseStart_3687100 : Nat := 118140960795 + 3687100 * 2 ^ 59
def prefixEnd_3687100 : Nat := 4983230072969 + 3 ^ 40 * 3687100 * 2
def baseEnd_3687100 : Nat := 420723226931695430665187

theorem tailTrace_3687100 : CollatzResearch.WordTrace tailWord_3687100 prefixEnd_3687100 420723226931695430665187 := by
  unfold tailWord_3687100
  simp only [CollatzResearch.WordTrace]
  refine ⟨67239792471136940695805377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89653056628182587594407169 67239792471136940695805377)
  ·
    refine ⟨50429844353352705521854033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67239792471136940695805377 50429844353352705521854033)
    ·
      refine ⟨37822383265014529141390525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50429844353352705521854033 37822383265014529141390525)
      ·
        refine ⟨14183393724380448428021447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37822383265014529141390525 14183393724380448428021447)
        ·
          refine ⟨21275090586570672642032171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14183393724380448428021447 21275090586570672642032171)
          ·
            refine ⟨31912635879856008963048257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21275090586570672642032171 31912635879856008963048257)
            ·
              refine ⟨23934476909892006722286193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31912635879856008963048257 23934476909892006722286193)
              ·
                refine ⟨17950857682419005041714645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23934476909892006722286193 17950857682419005041714645)
                ·
                  refine ⟨420723226931695430665187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17950857682419005041714645 420723226931695430665187)
                  ·
                    rfl

theorem cell22_3687100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 2, 7].length) (baseStart_3687100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687100 prefixEnd_3687100 := by exact prefixLift 3687100
  have htrace : WordTrace (prefixWord ++ tailWord_3687100) baseStart_3687100 baseEnd_3687100 := by
    simpa [prefixWord, tailWord_3687100, baseEnd_3687100] using wordTrace_append hprefix tailTrace_3687100
  have hstable : (prefixWord ++ tailWord_3687100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687100).length < 2 ^ (prefixWord ++ tailWord_3687100).sum := by decide
  have hdescent : baseEnd_3687100 < baseStart_3687100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687104 : List Nat := [2, 1, 1, 2, 4, 2, 1, 5, 1, 3]
def baseStart_3687104 : Nat := 118140960795 + 3687104 * 2 ^ 59
def prefixEnd_3687104 : Nat := 4983230072969 + 3 ^ 40 * 3687104 * 2
def baseEnd_3687104 : Nat := 1262171050076831614895549

theorem tailTrace_3687104 : CollatzResearch.WordTrace tailWord_3687104 prefixEnd_3687104 1262171050076831614895549 := by
  unfold tailWord_3687104
  simp only [CollatzResearch.WordTrace]
  refine ⟨67239865417129695037378183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89653153889506260049837577 67239865417129695037378183)
  ·
    refine ⟨100859798125694542556067275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67239865417129695037378183 100859798125694542556067275)
    ·
      refine ⟨151289697188541813834100913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100859798125694542556067275 151289697188541813834100913)
      ·
        refine ⟨113467272891406360375575685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151289697188541813834100913 113467272891406360375575685)
        ·
          refine ⟨21275113667138692570420441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113467272891406360375575685 21275113667138692570420441)
          ·
            refine ⟨15956335250354019427815331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21275113667138692570420441 15956335250354019427815331)
            ·
              refine ⟨23934502875531029141722997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15956335250354019427815331 23934502875531029141722997)
              ·
                refine ⟨2243859644581033982036531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23934502875531029141722997 2243859644581033982036531)
                ·
                  refine ⟨3365789466871550973054797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2243859644581033982036531 3365789466871550973054797)
                  ·
                    refine ⟨1262171050076831614895549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3365789466871550973054797 1262171050076831614895549)
                    ·
                      rfl

theorem cell22_3687104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 5, 1, 3].length) (baseStart_3687104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687104 prefixEnd_3687104 := by exact prefixLift 3687104
  have htrace : WordTrace (prefixWord ++ tailWord_3687104) baseStart_3687104 baseEnd_3687104 := by
    simpa [prefixWord, tailWord_3687104, baseEnd_3687104] using wordTrace_append hprefix tailTrace_3687104
  have hstable : (prefixWord ++ tailWord_3687104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687104).length < 2 ^ (prefixWord ++ tailWord_3687104).sum := by decide
  have hdescent : baseEnd_3687104 < baseStart_3687104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687110 : List Nat := [6, 1, 2, 1, 2, 2, 1, 2, 2, 3]
def baseStart_3687110 : Nat := 118140960795 + 3687110 * 2 ^ 59
def prefixEnd_3687110 : Nat := 4983230072969 + 3 ^ 40 * 3687110 * 2
def baseEnd_3687110 : Nat := 1262173103999449599245531

theorem tailTrace_3687110 : CollatzResearch.WordTrace tailWord_3687110 prefixEnd_3687110 1262173103999449599245531 := by
  unfold tailWord_3687110
  simp only [CollatzResearch.WordTrace]
  refine ⟨4202498427257426659358587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89653299781491768732983189 4202498427257426659358587)
  ·
    refine ⟨6303747640886139989037881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4202498427257426659358587 6303747640886139989037881)
    ·
      refine ⟨4727810730664604991778411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6303747640886139989037881 4727810730664604991778411)
      ·
        refine ⟨7091716095996907487667617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4727810730664604991778411 7091716095996907487667617)
        ·
          refine ⟨5318787071997680615750713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7091716095996907487667617 5318787071997680615750713)
          ·
            refine ⟨3989090303998260461813035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5318787071997680615750713 3989090303998260461813035)
            ·
              refine ⟨5983635455997390692719553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3989090303998260461813035 5983635455997390692719553)
              ·
                refine ⟨4487726591998043019539665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5983635455997390692719553 4487726591998043019539665)
                ·
                  refine ⟨3365794943998532264654749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4487726591998043019539665 3365794943998532264654749)
                  ·
                    refine ⟨1262173103999449599245531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3365794943998532264654749 1262173103999449599245531)
                    ·
                      rfl

theorem cell22_3687110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_3687110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687110 prefixEnd_3687110 := by exact prefixLift 3687110
  have htrace : WordTrace (prefixWord ++ tailWord_3687110) baseStart_3687110 baseEnd_3687110 := by
    simpa [prefixWord, tailWord_3687110, baseEnd_3687110] using wordTrace_append hprefix tailTrace_3687110
  have hstable : (prefixWord ++ tailWord_3687110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687110).length < 2 ^ (prefixWord ++ tailWord_3687110).sum := by decide
  have hdescent : baseEnd_3687110 < baseStart_3687110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687145 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 6]
def baseStart_3687145 : Nat := 118140960795 + 3687145 * 2 ^ 59
def prefixEnd_3687145 : Nat := 4983230072969 + 3 ^ 40 * 3687145 * 2
def baseEnd_3687145 : Nat := 420728361738240391540141

theorem tailTrace_3687145 : CollatzResearch.WordTrace tailWord_3687145 prefixEnd_3687145 420728361738240391540141 := by
  unfold tailWord_3687145
  simp only [CollatzResearch.WordTrace]
  refine ⟨134481226227110854076998889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89654150818073902717999259 134481226227110854076998889)
  ·
    refine ⟨100860919670333140557749167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134481226227110854076998889 100860919670333140557749167)
    ·
      refine ⟨151291379505499710836623751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100860919670333140557749167 151291379505499710836623751)
      ·
        refine ⟨226937069258249566254935627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151291379505499710836623751 226937069258249566254935627)
        ·
          refine ⟨340405603887374349382403441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226937069258249566254935627 340405603887374349382403441)
          ·
            refine ⟨255304202915530762036802581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340405603887374349382403441 255304202915530762036802581)
            ·
              refine ⟨11967384511665504470475121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 255304202915530762036802581 11967384511665504470475121)
              ·
                refine ⟨8975538383749128352856341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11967384511665504470475121 8975538383749128352856341)
                ·
                  refine ⟨420728361738240391540141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8975538383749128352856341 420728361738240391540141)
                  ·
                    rfl

theorem cell22_3687145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 6].length) (baseStart_3687145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687145 prefixEnd_3687145 := by exact prefixLift 3687145
  have htrace : WordTrace (prefixWord ++ tailWord_3687145) baseStart_3687145 baseEnd_3687145 := by
    simpa [prefixWord, tailWord_3687145, baseEnd_3687145] using wordTrace_append hprefix tailTrace_3687145
  have hstable : (prefixWord ++ tailWord_3687145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687145).length < 2 ^ (prefixWord ++ tailWord_3687145).sum := by decide
  have hdescent : baseEnd_3687145 < baseStart_3687145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687160 : List Nat := [2, 1, 2, 1, 1, 2, 4, 1, 3, 5]
def baseStart_3687160 : Nat := 118140960795 + 3687160 * 2 ^ 59
def prefixEnd_3687160 : Nat := 4983230072969 + 3 ^ 40 * 3687160 * 2
def baseEnd_3687160 : Nat := 1262190220021266135495377

theorem tailTrace_3687160 : CollatzResearch.WordTrace tailWord_3687160 prefixEnd_3687160 1262190220021266135495377 := by
  unfold tailWord_3687160
  simp only [CollatzResearch.WordTrace]
  refine ⟨67240886661028255819397467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89654515548037674425863289 67240886661028255819397467)
  ·
    refine ⟨100861329991542383729096201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67240886661028255819397467 100861329991542383729096201)
    ·
      refine ⟨75645997493656787796822151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100861329991542383729096201 75645997493656787796822151)
      ·
        refine ⟨113468996240485181695233227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75645997493656787796822151 113468996240485181695233227)
        ·
          refine ⟨170203494360727772542849841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113468996240485181695233227 170203494360727772542849841)
          ·
            refine ⟨127652620770545829407137381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170203494360727772542849841 127652620770545829407137381)
            ·
              refine ⟨23934866394477343013838259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127652620770545829407137381 23934866394477343013838259)
              ·
                refine ⟨35902299591716014520757389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23934866394477343013838259 35902299591716014520757389)
                ·
                  refine ⟨13463362346893505445284021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35902299591716014520757389 13463362346893505445284021)
                  ·
                    refine ⟨1262190220021266135495377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13463362346893505445284021 1262190220021266135495377)
                    ·
                      rfl

theorem cell22_3687160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_3687160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687160 prefixEnd_3687160 := by exact prefixLift 3687160
  have htrace : WordTrace (prefixWord ++ tailWord_3687160) baseStart_3687160 baseEnd_3687160 := by
    simpa [prefixWord, tailWord_3687160, baseEnd_3687160] using wordTrace_append hprefix tailTrace_3687160
  have hstable : (prefixWord ++ tailWord_3687160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687160).length < 2 ^ (prefixWord ++ tailWord_3687160).sum := by decide
  have hdescent : baseEnd_3687160 < baseStart_3687160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687177 : List Nat := [1, 2, 1, 1, 3, 2, 4, 1, 4, 3]
def baseStart_3687177 : Nat := 118140960795 + 3687177 * 2 ^ 59
def prefixEnd_3687177 : Nat := 4983230072969 + 3 ^ 40 * 3687177 * 2
def baseEnd_3687177 : Nat := 1262196039468683757820325

theorem tailTrace_3687177 : CollatzResearch.WordTrace tailWord_3687177 prefixEnd_3687177 1262196039468683757820325 := by
  unfold tailWord_3687177
  simp only [CollatzResearch.WordTrace]
  refine ⟨134482393362994923542163785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89654928908663282361442523 134482393362994923542163785)
  ·
    refine ⟨100861795022246192656622839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134482393362994923542163785 100861795022246192656622839)
    ·
      refine ⟨151292692533369288984934259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100861795022246192656622839 151292692533369288984934259)
      ·
        refine ⟨226939038800053933477401389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151292692533369288984934259 226939038800053933477401389)
        ·
          refine ⟨85102139550020225054025521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226939038800053933477401389 85102139550020225054025521)
          ·
            refine ⟨63826604662515168790519141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85102139550020225054025521 63826604662515168790519141)
            ·
              refine ⟨11967488374221594148222339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63826604662515168790519141 11967488374221594148222339)
              ·
                refine ⟨17951232561332391222333509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11967488374221594148222339 17951232561332391222333509)
                ·
                  refine ⟨3365856105249823354187533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17951232561332391222333509 3365856105249823354187533)
                  ·
                    refine ⟨1262196039468683757820325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3365856105249823354187533 1262196039468683757820325)
                    ·
                      rfl

theorem cell22_3687177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 1, 4, 3].length) (baseStart_3687177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687177 prefixEnd_3687177 := by exact prefixLift 3687177
  have htrace : WordTrace (prefixWord ++ tailWord_3687177) baseStart_3687177 baseEnd_3687177 := by
    simpa [prefixWord, tailWord_3687177, baseEnd_3687177] using wordTrace_append hprefix tailTrace_3687177
  have hstable : (prefixWord ++ tailWord_3687177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687177).length < 2 ^ (prefixWord ++ tailWord_3687177).sum := by decide
  have hdescent : baseEnd_3687177 < baseStart_3687177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687194 : List Nat := [3, 1, 1, 3, 2, 1, 3, 3, 2, 3]
def baseStart_3687194 : Nat := 118140960795 + 3687194 * 2 ^ 59
def prefixEnd_3687194 : Nat := 4983230072969 + 3 ^ 40 * 3687194 * 2
def baseEnd_3687194 : Nat := 1262201858916101380145273

theorem tailTrace_3687194 : CollatzResearch.WordTrace tailWord_3687194 prefixEnd_3687194 1262201858916101380145273 := by
  unfold tailWord_3687194
  simp only [CollatzResearch.WordTrace]
  refine ⟨33620753350983333861383159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89655342269288890297021757 33620753350983333861383159)
  ·
    refine ⟨50431130026475000792074739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33620753350983333861383159 50431130026475000792074739)
    ·
      refine ⟨75646695039712501188112109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50431130026475000792074739 75646695039712501188112109)
      ·
        refine ⟨28367510639892187945542041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75646695039712501188112109 28367510639892187945542041)
        ·
          refine ⟨21275632979919140959156531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28367510639892187945542041 21275632979919140959156531)
          ·
            refine ⟨31913449469878711438734797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21275632979919140959156531 31913449469878711438734797)
            ·
              refine ⟨11967543551204516789525549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31913449469878711438734797 11967543551204516789525549)
              ·
                refine ⟨4487828831701693796072081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11967543551204516789525549 4487828831701693796072081)
                ·
                  refine ⟨3365871623776270347054061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4487828831701693796072081 3365871623776270347054061)
                  ·
                    refine ⟨1262201858916101380145273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3365871623776270347054061 1262201858916101380145273)
                    ·
                      rfl

theorem cell22_3687194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 3, 2, 3].length) (baseStart_3687194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687194 prefixEnd_3687194 := by exact prefixLift 3687194
  have htrace : WordTrace (prefixWord ++ tailWord_3687194) baseStart_3687194 baseEnd_3687194 := by
    simpa [prefixWord, tailWord_3687194, baseEnd_3687194] using wordTrace_append hprefix tailTrace_3687194
  have hstable : (prefixWord ++ tailWord_3687194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687194).length < 2 ^ (prefixWord ++ tailWord_3687194).sum := by decide
  have hdescent : baseEnd_3687194 < baseStart_3687194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687230 : List Nat := [4, 2, 1, 2, 4, 1, 2, 2, 4]
def baseStart_3687230 : Nat := 118140960795 + 3687230 * 2 ^ 59
def prefixEnd_3687230 : Nat := 4983230072969 + 3 ^ 40 * 3687230 * 2
def baseEnd_3687230 : Nat := 420738060817269762081721

theorem tailTrace_3687230 : CollatzResearch.WordTrace tailWord_3687230 prefixEnd_3687230 420738060817269762081721 := by
  unfold tailWord_3687230
  simp only [CollatzResearch.WordTrace]
  refine ⟨16810540803975364199230393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89656217621201942395895429 16810540803975364199230393)
  ·
    refine ⟨12607905602981523149422795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16810540803975364199230393 12607905602981523149422795)
    ·
      refine ⟨18911858404472284724134193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12607905602981523149422795 18911858404472284724134193)
      ·
        refine ⟨14183893803354213543100645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18911858404472284724134193 14183893803354213543100645)
        ·
          refine ⟨2659480088128915039331371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14183893803354213543100645 2659480088128915039331371)
          ·
            refine ⟨3989220132193372558997057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2659480088128915039331371 3989220132193372558997057)
            ·
              refine ⟨2991915099145029419247793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3989220132193372558997057 2991915099145029419247793)
              ·
                refine ⟨2243936324358772064435845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2991915099145029419247793 2243936324358772064435845)
                ·
                  refine ⟨420738060817269762081721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2243936324358772064435845 420738060817269762081721)
                  ·
                    rfl

theorem cell22_3687230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_3687230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687230 prefixEnd_3687230 := by exact prefixLift 3687230
  have htrace : WordTrace (prefixWord ++ tailWord_3687230) baseStart_3687230 baseEnd_3687230 := by
    simpa [prefixWord, tailWord_3687230, baseEnd_3687230] using wordTrace_append hprefix tailTrace_3687230
  have hstable : (prefixWord ++ tailWord_3687230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687230).length < 2 ^ (prefixWord ++ tailWord_3687230).sum := by decide
  have hdescent : baseEnd_3687230 < baseStart_3687230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687286 : List Nat := [5, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_3687286 : Nat := 118140960795 + 3687286 * 2 ^ 59
def prefixEnd_3687286 : Nat := 4983230072969 + 3 ^ 40 * 3687286 * 2
def baseEnd_3687286 : Nat := 420744450798747935614997

theorem tailTrace_3687286 : CollatzResearch.WordTrace tailWord_3687286 prefixEnd_3687286 420744450798747935614997 := by
  unfold tailWord_3687286
  simp only [CollatzResearch.WordTrace]
  refine ⟨8405398057475002197367607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89657579279733356771921141 8405398057475002197367607)
  ·
    refine ⟨12608097086212503296051411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8405398057475002197367607 12608097086212503296051411)
    ·
      refine ⟨18912145629318754944077117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12608097086212503296051411 18912145629318754944077117)
      ·
        refine ⟨7092054610994533104028919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18912145629318754944077117 7092054610994533104028919)
        ·
          refine ⟨10638081916491799656043379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7092054610994533104028919 10638081916491799656043379)
          ·
            refine ⟨15957122874737699484065069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10638081916491799656043379 15957122874737699484065069)
            ·
              refine ⟨5983921078026637306524401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15957122874737699484065069 5983921078026637306524401)
              ·
                refine ⟨4487940808519977979893301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5983921078026637306524401 4487940808519977979893301)
                ·
                  refine ⟨420744450798747935614997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4487940808519977979893301 420744450798747935614997)
                  ·
                    rfl

theorem cell22_3687286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_3687286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687286 prefixEnd_3687286 := by exact prefixLift 3687286
  have htrace : WordTrace (prefixWord ++ tailWord_3687286) baseStart_3687286 baseEnd_3687286 := by
    simpa [prefixWord, tailWord_3687286, baseEnd_3687286] using wordTrace_append hprefix tailTrace_3687286
  have hstable : (prefixWord ++ tailWord_3687286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687286).length < 2 ^ (prefixWord ++ tailWord_3687286).sum := by decide
  have hdescent : baseEnd_3687286 < baseStart_3687286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687316 : List Nat := [2, 4, 2, 1, 1, 1, 4, 2, 1, 4]
def baseStart_3687316 : Nat := 118140960795 + 3687316 * 2 ^ 59
def prefixEnd_3687316 : Nat := 4983230072969 + 3 ^ 40 * 3687316 * 2
def baseEnd_3687316 : Nat := 1262243622009333728594899

theorem tailTrace_3687316 : CollatzResearch.WordTrace tailWord_3687316 prefixEnd_3687316 1262243622009333728594899 := by
  unfold tailWord_3687316
  simp only [CollatzResearch.WordTrace]
  refine ⟨67243731554745675140736901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89658308739660900187649201 67243731554745675140736901)
  ·
    refine ⟨12608199666514814088888169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67243731554745675140736901 12608199666514814088888169)
    ·
      refine ⟨9456149749886110566666127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12608199666514814088888169 9456149749886110566666127)
      ·
        refine ⟨14184224624829165849999191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9456149749886110566666127 14184224624829165849999191)
        ·
          refine ⟨21276336937243748774998787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14184224624829165849999191 21276336937243748774998787)
          ·
            refine ⟨31914505405865623162498181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21276336937243748774998787 31914505405865623162498181)
            ·
              refine ⟨5983969763599804342968409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31914505405865623162498181 5983969763599804342968409)
              ·
                refine ⟨4487977322699853257226307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5983969763599804342968409 4487977322699853257226307)
                ·
                  refine ⟨6731965984049779885839461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4487977322699853257226307 6731965984049779885839461)
                  ·
                    refine ⟨1262243622009333728594899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6731965984049779885839461 1262243622009333728594899)
                    ·
                      rfl

theorem cell22_3687316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_3687316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687316 prefixEnd_3687316 := by exact prefixLift 3687316
  have htrace : WordTrace (prefixWord ++ tailWord_3687316) baseStart_3687316 baseEnd_3687316 := by
    simpa [prefixWord, tailWord_3687316, baseEnd_3687316] using wordTrace_append hprefix tailTrace_3687316
  have hstable : (prefixWord ++ tailWord_3687316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687316).length < 2 ^ (prefixWord ++ tailWord_3687316).sum := by decide
  have hdescent : baseEnd_3687316 < baseStart_3687316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687348 : List Nat := [2, 5, 2, 1, 1, 3, 1, 1, 6]
def baseStart_3687348 : Nat := 118140960795 + 3687348 * 2 ^ 59
def prefixEnd_3687348 : Nat := 4983230072969 + 3 ^ 40 * 3687348 * 2
def baseEnd_3687348 : Nat := 420751525421098770598267

theorem tailTrace_3687348 : CollatzResearch.WordTrace tailWord_3687348 prefixEnd_3687348 420751525421098770598267 := by
  unfold tailWord_3687348
  simp only [CollatzResearch.WordTrace]
  refine ⟨67244315122687709873319349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89659086830250279831092465 67244315122687709873319349)
  ·
    refine ⟨6304154542751972800623689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67244315122687709873319349 6304154542751972800623689)
    ·
      refine ⟨4728115907063979600467767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6304154542751972800623689 4728115907063979600467767)
      ·
        refine ⟨7092173860595969400701651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4728115907063979600467767 7092173860595969400701651)
        ·
          refine ⟨10638260790893954101052477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7092173860595969400701651 10638260790893954101052477)
          ·
            refine ⟨3989347796585232787894679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10638260790893954101052477 3989347796585232787894679)
            ·
              refine ⟨5984021694877849181842019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3989347796585232787894679 5984021694877849181842019)
              ·
                refine ⟨8976032542316773772763029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5984021694877849181842019 8976032542316773772763029)
                ·
                  refine ⟨420751525421098770598267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8976032542316773772763029 420751525421098770598267)
                  ·
                    rfl

theorem cell22_3687348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_3687348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687348 prefixEnd_3687348 := by exact prefixLift 3687348
  have htrace : WordTrace (prefixWord ++ tailWord_3687348) baseStart_3687348 baseEnd_3687348 := by
    simpa [prefixWord, tailWord_3687348, baseEnd_3687348] using wordTrace_append hprefix tailTrace_3687348
  have hstable : (prefixWord ++ tailWord_3687348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687348).length < 2 ^ (prefixWord ++ tailWord_3687348).sum := by decide
  have hdescent : baseEnd_3687348 < baseStart_3687348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687481 : List Nat := [1, 2, 1, 5, 2, 1, 3, 1, 1, 5]
def baseStart_3687481 : Nat := 118140960795 + 3687481 * 2 ^ 59
def prefixEnd_3687481 : Nat := 4983230072969 + 3 ^ 40 * 3687481 * 2
def baseEnd_3687481 : Nat := 1262300104881328298219393

theorem tailTrace_3687481 : CollatzResearch.WordTrace tailWord_3687481 prefixEnd_3687481 1262300104881328298219393 := by
  unfold tailWord_3687481
  simp only [CollatzResearch.WordTrace]
  refine ⟨134493481153893583461230297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89662320769262388974153531 134493481153893583461230297)
  ·
    refine ⟨100870110865420187595922723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134493481153893583461230297 100870110865420187595922723)
    ·
      refine ⟨151305166298130281393884085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100870110865420187595922723 151305166298130281393884085)
      ·
        refine ⟨14184859340449713880676633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 151305166298130281393884085 14184859340449713880676633)
        ·
          refine ⟨10638644505337285410507475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14184859340449713880676633 10638644505337285410507475)
          ·
            refine ⟨15957966758005928115761213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10638644505337285410507475 15957966758005928115761213)
            ·
              refine ⟨5984237534252223043410455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15957966758005928115761213 5984237534252223043410455)
              ·
                refine ⟨8976356301378334565115683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5984237534252223043410455 8976356301378334565115683)
                ·
                  refine ⟨13464534452067501847673525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8976356301378334565115683 13464534452067501847673525)
                  ·
                    refine ⟨1262300104881328298219393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13464534452067501847673525 1262300104881328298219393)
                    ·
                      rfl

theorem cell22_3687481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_3687481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687481 prefixEnd_3687481 := by exact prefixLift 3687481
  have htrace : WordTrace (prefixWord ++ tailWord_3687481) baseStart_3687481 baseEnd_3687481 := by
    simpa [prefixWord, tailWord_3687481, baseEnd_3687481] using wordTrace_append hprefix tailTrace_3687481
  have hstable : (prefixWord ++ tailWord_3687481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687481).length < 2 ^ (prefixWord ++ tailWord_3687481).sum := by decide
  have hdescent : baseEnd_3687481 < baseStart_3687481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687517 : List Nat := [1, 4, 4, 1, 2, 1, 3, 2, 4]
def baseStart_3687517 : Nat := 118140960795 + 3687517 * 2 ^ 59
def prefixEnd_3687517 : Nat := 4983230072969 + 3 ^ 40 * 3687517 * 2
def baseEnd_3687517 : Nat := 420770809472345401439761

theorem tailTrace_3687517 : CollatzResearch.WordTrace tailWord_3687517 prefixEnd_3687517 420770809472345401439761 := by
  unfold tailWord_3687517
  simp only [CollatzResearch.WordTrace]
  refine ⟨134494794181763161609540805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89663196121175441073027203 134494794181763161609540805)
  ·
    refine ⟨25217773909080592801788901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134494794181763161609540805 25217773909080592801788901)
    ·
      refine ⟨4728332607952611150335419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25217773909080592801788901 4728332607952611150335419)
      ·
        refine ⟨7092498911928916725503129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4728332607952611150335419 7092498911928916725503129)
        ·
          refine ⟨5319374183946687544127347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7092498911928916725503129 5319374183946687544127347)
          ·
            refine ⟨7979061275920031316191021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5319374183946687544127347 7979061275920031316191021)
            ·
              refine ⟨2992147978470011743571633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7979061275920031316191021 2992147978470011743571633)
              ·
                refine ⟨2244110983852508807678725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2992147978470011743571633 2244110983852508807678725)
                ·
                  refine ⟨420770809472345401439761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2244110983852508807678725 420770809472345401439761)
                  ·
                    rfl

theorem cell22_3687517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_3687517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687517 prefixEnd_3687517 := by exact prefixLift 3687517
  have htrace : WordTrace (prefixWord ++ tailWord_3687517) baseStart_3687517 baseEnd_3687517 := by
    simpa [prefixWord, tailWord_3687517, baseEnd_3687517] using wordTrace_append hprefix tailTrace_3687517
  have hstable : (prefixWord ++ tailWord_3687517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687517).length < 2 ^ (prefixWord ++ tailWord_3687517).sum := by decide
  have hdescent : baseEnd_3687517 < baseStart_3687517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687524 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_3687524 : Nat := 118140960795 + 3687524 * 2 ^ 59
def prefixEnd_3687524 : Nat := 4983230072969 + 3 ^ 40 * 3687524 * 2
def baseEnd_3687524 : Nat := 1262314824660090519394261

theorem tailTrace_3687524 : CollatzResearch.WordTrace tailWord_3687524 prefixEnd_3687524 1262314824660090519394261 := by
  unfold tailWord_3687524
  simp only [CollatzResearch.WordTrace]
  refine ⟨67247524746368900902522813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89663366328491867870030417 67247524746368900902522813)
  ·
    refine ⟨25217821779888337838446055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67247524746368900902522813 25217821779888337838446055)
    ·
      refine ⟨37826732669832506757669083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25217821779888337838446055 37826732669832506757669083)
      ·
        refine ⟨56740099004748760136503625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37826732669832506757669083 56740099004748760136503625)
        ·
          refine ⟨42555074253561570102377719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56740099004748760136503625 42555074253561570102377719)
          ·
            refine ⟨63832611380342355153566579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42555074253561570102377719 63832611380342355153566579)
            ·
              refine ⟨95748917070513532730349869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63832611380342355153566579 95748917070513532730349869)
              ·
                refine ⟨35905843901442574773881201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95748917070513532730349869 35905843901442574773881201)
                ·
                  refine ⟨26929382926081931080410901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35905843901442574773881201 26929382926081931080410901)
                  ·
                    refine ⟨1262314824660090519394261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26929382926081931080410901 1262314824660090519394261)
                    ·
                      rfl

theorem cell22_3687524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_3687524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687524 prefixEnd_3687524 := by exact prefixLift 3687524
  have htrace : WordTrace (prefixWord ++ tailWord_3687524) baseStart_3687524 baseEnd_3687524 := by
    simpa [prefixWord, tailWord_3687524, baseEnd_3687524] using wordTrace_append hprefix tailTrace_3687524
  have hstable : (prefixWord ++ tailWord_3687524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687524).length < 2 ^ (prefixWord ++ tailWord_3687524).sum := by decide
  have hdescent : baseEnd_3687524 < baseStart_3687524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687528 : List Nat := [2, 1, 4, 4, 1, 1, 2, 7]
def baseStart_3687528 : Nat := 118140960795 + 3687528 * 2 ^ 59
def prefixEnd_3687528 : Nat := 4983230072969 + 3 ^ 40 * 3687528 * 2
def baseEnd_3687528 : Nat := 140257354882426204699361

theorem tailTrace_3687528 : CollatzResearch.WordTrace tailWord_3687528 prefixEnd_3687528 140257354882426204699361 := by
  unfold tailWord_3687528
  simp only [CollatzResearch.WordTrace]
  refine ⟨67247597692361655244095619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89663463589815540325460825 67247597692361655244095619)
  ·
    refine ⟨100871396538542482866143429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67247597692361655244095619 100871396538542482866143429)
    ·
      refine ⟨18913386850976715537401893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100871396538542482866143429 18913386850976715537401893)
      ·
        refine ⟨3546260034558134163262855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18913386850976715537401893 3546260034558134163262855)
        ·
          refine ⟨5319390051837201244894283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3546260034558134163262855 5319390051837201244894283)
          ·
            refine ⟨7979085077755801867341425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5319390051837201244894283 7979085077755801867341425)
            ·
              refine ⟨5984313808316851400506069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7979085077755801867341425 5984313808316851400506069)
              ·
                refine ⟨140257354882426204699361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5984313808316851400506069 140257354882426204699361)
                ·
                  rfl

theorem cell22_3687528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 7].length) (baseStart_3687528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687528 prefixEnd_3687528 := by exact prefixLift 3687528
  have htrace : WordTrace (prefixWord ++ tailWord_3687528) baseStart_3687528 baseEnd_3687528 := by
    simpa [prefixWord, tailWord_3687528, baseEnd_3687528] using wordTrace_append hprefix tailTrace_3687528
  have hstable : (prefixWord ++ tailWord_3687528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687528).length < 2 ^ (prefixWord ++ tailWord_3687528).sum := by decide
  have hdescent : baseEnd_3687528 < baseStart_3687528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687601 : List Nat := [1, 2, 2, 5, 1, 1, 1, 1, 8]
def baseStart_3687601 : Nat := 118140960795 + 3687601 * 2 ^ 59
def prefixEnd_3687601 : Nat := 4983230072969 + 3 ^ 40 * 3687601 * 2
def baseEnd_3687601 : Nat := 420780394444562661739675

theorem tailTrace_3687601 : CollatzResearch.WordTrace tailWord_3687601 prefixEnd_3687601 420780394444562661739675 := by
  unfold tailWord_3687601
  simp only [CollatzResearch.WordTrace]
  refine ⟨134497857913458843955598657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89665238608972562637065771 134497857913458843955598657)
  ·
    refine ⟨100873393435094132966698993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134497857913458843955598657 100873393435094132966698993)
    ·
      refine ⟨75655045076320599725024245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100873393435094132966698993 75655045076320599725024245)
      ·
        refine ⟨7092660475905056224221023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75655045076320599725024245 7092660475905056224221023)
        ·
          refine ⟨10638990713857584336331535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7092660475905056224221023 10638990713857584336331535)
          ·
            refine ⟨15958486070786376504497303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10638990713857584336331535 15958486070786376504497303)
            ·
              refine ⟨23937729106179564756745955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15958486070786376504497303 23937729106179564756745955)
              ·
                refine ⟨35906593659269347135118933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23937729106179564756745955 35906593659269347135118933)
                ·
                  refine ⟨420780394444562661739675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35906593659269347135118933 420780394444562661739675)
                  ·
                    rfl

theorem cell22_3687601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 1, 8].length) (baseStart_3687601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687601 prefixEnd_3687601 := by exact prefixLift 3687601
  have htrace : WordTrace (prefixWord ++ tailWord_3687601) baseStart_3687601 baseEnd_3687601 := by
    simpa [prefixWord, tailWord_3687601, baseEnd_3687601] using wordTrace_append hprefix tailTrace_3687601
  have hstable : (prefixWord ++ tailWord_3687601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687601).length < 2 ^ (prefixWord ++ tailWord_3687601).sum := by decide
  have hdescent : baseEnd_3687601 < baseStart_3687601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687620 : List Nat := [2, 3, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_3687620 : Nat := 118140960795 + 3687620 * 2 ^ 59
def prefixEnd_3687620 : Nat := 4983230072969 + 3 ^ 40 * 3687620 * 2
def baseEnd_3687620 : Nat := 1262347687421978268993967

theorem tailTrace_3687620 : CollatzResearch.WordTrace tailWord_3687620 prefixEnd_3687620 1262347687421978268993967 := by
  unfold tailWord_3687620
  simp only [CollatzResearch.WordTrace]
  refine ⟨67249275450195005100270157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89665700600260006800360209 67249275450195005100270157)
  ·
    refine ⟨25218478293823126912601309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67249275450195005100270157 25218478293823126912601309)
    ·
      refine ⟨9456929360183672592225491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25218478293823126912601309 9456929360183672592225491)
      ·
        refine ⟨14185394040275508888338237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9456929360183672592225491 14185394040275508888338237)
        ·
          refine ⟨5319522765103315833126839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14185394040275508888338237 5319522765103315833126839)
          ·
            refine ⟨7979284147654973749690259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5319522765103315833126839 7979284147654973749690259)
            ·
              refine ⟨11968926221482460624535389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7979284147654973749690259 11968926221482460624535389)
              ·
                refine ⟨4488347333055922734200771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11968926221482460624535389 4488347333055922734200771)
                ·
                  refine ⟨6732520999583884101301157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4488347333055922734200771 6732520999583884101301157)
                  ·
                    refine ⟨1262347687421978268993967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6732520999583884101301157 1262347687421978268993967)
                    ·
                      rfl

theorem cell22_3687620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_3687620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687620 prefixEnd_3687620 := by exact prefixLift 3687620
  have htrace : WordTrace (prefixWord ++ tailWord_3687620) baseStart_3687620 baseEnd_3687620 := by
    simpa [prefixWord, tailWord_3687620, baseEnd_3687620] using wordTrace_append hprefix tailTrace_3687620
  have hstable : (prefixWord ++ tailWord_3687620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687620).length < 2 ^ (prefixWord ++ tailWord_3687620).sum := by decide
  have hdescent : baseEnd_3687620 < baseStart_3687620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687691 : List Nat := [1, 1, 1, 1, 5, 3, 2, 1, 7]
def baseStart_3687691 : Nat := 118140960795 + 3687691 * 2 ^ 59
def prefixEnd_3687691 : Nat := 4983230072969 + 3 ^ 40 * 3687691 * 2
def baseEnd_3687691 : Nat := 420790664057652583489583

theorem tailTrace_3687691 : CollatzResearch.WordTrace tailWord_3687691 prefixEnd_3687691 420790664057652583489583 := by
  unfold tailWord_3687691
  simp only [CollatzResearch.WordTrace]
  refine ⟨134501140483132789326374927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89667426988755192884249951 134501140483132789326374927)
  ·
    refine ⟨201751710724699183989562391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134501140483132789326374927 201751710724699183989562391)
    ·
      refine ⟨302627566087048775984343587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201751710724699183989562391 302627566087048775984343587)
      ·
        refine ⟨453941349130573163976515381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302627566087048775984343587 453941349130573163976515381)
        ·
          refine ⟨42557001480991234122798317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 453941349130573163976515381 42557001480991234122798317)
          ·
            refine ⟨15958875555371712796049369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42557001480991234122798317 15958875555371712796049369)
            ·
              refine ⟨11969156666528784597037027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15958875555371712796049369 11969156666528784597037027)
              ·
                refine ⟨17953734999793176895555541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11969156666528784597037027 17953734999793176895555541)
                ·
                  refine ⟨420790664057652583489583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17953734999793176895555541 420790664057652583489583)
                  ·
                    rfl

theorem cell22_3687691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 1, 7].length) (baseStart_3687691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687691 prefixEnd_3687691 := by exact prefixLift 3687691
  have htrace : WordTrace (prefixWord ++ tailWord_3687691) baseStart_3687691 baseEnd_3687691 := by
    simpa [prefixWord, tailWord_3687691, baseEnd_3687691] using wordTrace_append hprefix tailTrace_3687691
  have hstable : (prefixWord ++ tailWord_3687691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687691).length < 2 ^ (prefixWord ++ tailWord_3687691).sum := by decide
  have hdescent : baseEnd_3687691 < baseStart_3687691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687757 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 2, 5]
def baseStart_3687757 : Nat := 118140960795 + 3687757 * 2 ^ 59
def prefixEnd_3687757 : Nat := 4983230072969 + 3 ^ 40 * 3687757 * 2
def baseEnd_3687757 : Nat := 1262394585321755578318547

theorem tailTrace_3687757 : CollatzResearch.WordTrace tailWord_3687757 prefixEnd_3687757 1262394585321755578318547 := by
  unfold tailWord_3687757
  simp only [CollatzResearch.WordTrace]
  refine ⟨134503547700893682598277525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89669031800595788398851683 134503547700893682598277525)
  ·
    refine ⟨6304853798479391371794259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 134503547700893682598277525 6304853798479391371794259)
    ·
      refine ⟨9457280697719087057691389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6304853798479391371794259 9457280697719087057691389)
      ·
        refine ⟨3546480261644657646634271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9457280697719087057691389 3546480261644657646634271)
        ·
          refine ⟨5319720392466986469951407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3546480261644657646634271 5319720392466986469951407)
          ·
            refine ⟨7979580588700479704927111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5319720392466986469951407 7979580588700479704927111)
            ·
              refine ⟨11969370883050719557390667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7979580588700479704927111 11969370883050719557390667)
              ·
                refine ⟨17954056324576079336086001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11969370883050719557390667 17954056324576079336086001)
                ·
                  refine ⟨13465542243432059502064501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17954056324576079336086001 13465542243432059502064501)
                  ·
                    refine ⟨1262394585321755578318547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13465542243432059502064501 1262394585321755578318547)
                    ·
                      rfl

theorem cell22_3687757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_3687757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687757 prefixEnd_3687757 := by exact prefixLift 3687757
  have htrace : WordTrace (prefixWord ++ tailWord_3687757) baseStart_3687757 baseEnd_3687757 := by
    simpa [prefixWord, tailWord_3687757, baseEnd_3687757] using wordTrace_append hprefix tailTrace_3687757
  have hstable : (prefixWord ++ tailWord_3687757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687757).length < 2 ^ (prefixWord ++ tailWord_3687757).sum := by decide
  have hdescent : baseEnd_3687757 < baseStart_3687757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687768 : List Nat := [2, 1, 2, 2, 1, 1, 6, 1, 1, 5]
def baseStart_3687768 : Nat := 118140960795 + 3687768 * 2 ^ 59
def prefixEnd_3687768 : Nat := 4983230072969 + 3 ^ 40 * 3687768 * 2
def baseEnd_3687768 : Nat := 1262398350846555216293513

theorem tailTrace_3687768 : CollatzResearch.WordTrace tailWord_3687768 prefixEnd_3687768 1262398350846555216293513 := by
  unfold tailWord_3687768
  simp only [CollatzResearch.WordTrace]
  refine ⟨67251974451926915738463979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89669299269235887651285305 67251974451926915738463979)
  ·
    refine ⟨100877961677890373607695969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67251974451926915738463979 100877961677890373607695969)
    ·
      refine ⟨75658471258417780205771977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100877961677890373607695969 75658471258417780205771977)
      ·
        refine ⟨56743853443813335154328983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75658471258417780205771977 56743853443813335154328983)
        ·
          refine ⟨85115780165720002731493475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56743853443813335154328983 85115780165720002731493475)
          ·
            refine ⟨127673670248580004097240213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85115780165720002731493475 127673670248580004097240213)
            ·
              refine ⟨5984703292902187692058135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127673670248580004097240213 5984703292902187692058135)
              ·
                refine ⟨8977054939353281538087203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5984703292902187692058135 8977054939353281538087203)
                ·
                  refine ⟨13465582409029922307130805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8977054939353281538087203 13465582409029922307130805)
                  ·
                    refine ⟨1262398350846555216293513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13465582409029922307130805 1262398350846555216293513)
                    ·
                      rfl

theorem cell22_3687768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_3687768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687768 prefixEnd_3687768 := by exact prefixLift 3687768
  have htrace : WordTrace (prefixWord ++ tailWord_3687768) baseStart_3687768 baseEnd_3687768 := by
    simpa [prefixWord, tailWord_3687768, baseEnd_3687768] using wordTrace_append hprefix tailTrace_3687768
  have hstable : (prefixWord ++ tailWord_3687768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687768).length < 2 ^ (prefixWord ++ tailWord_3687768).sum := by decide
  have hdescent : baseEnd_3687768 < baseStart_3687768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687832 : List Nat := [2, 1, 2, 5, 2, 2, 2, 6]
def baseStart_3687832 : Nat := 118140960795 + 3687832 * 2 ^ 59
def prefixEnd_3687832 : Nat := 4983230072969 + 3 ^ 40 * 3687832 * 2
def baseEnd_3687832 : Nat := 140268917706053375854813

theorem tailTrace_3687832 : CollatzResearch.WordTrace tailWord_3687832 prefixEnd_3687832 140268917706053375854813 := by
  unfold tailWord_3687832
  simp only [CollatzResearch.WordTrace]
  refine ⟨67253141587810985203628875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89670855450414646938171833 67253141587810985203628875)
  ·
    refine ⟨100879712381716477805443313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67253141587810985203628875 100879712381716477805443313)
    ·
      refine ⟨75659784286287358354082485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100879712381716477805443313 75659784286287358354082485)
      ·
        refine ⟨7093104776839439845695233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75659784286287358354082485 7093104776839439845695233)
        ·
          refine ⟨5319828582629579884271425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7093104776839439845695233 5319828582629579884271425)
          ·
            refine ⟨3989871436972184913203569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5319828582629579884271425 3989871436972184913203569)
            ·
              refine ⟨2992403577729138684902677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3989871436972184913203569 2992403577729138684902677)
              ·
                refine ⟨140268917706053375854813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2992403577729138684902677 140268917706053375854813)
                ·
                  rfl

theorem cell22_3687832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 6].length) (baseStart_3687832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687832 prefixEnd_3687832 := by exact prefixLift 3687832
  have htrace : WordTrace (prefixWord ++ tailWord_3687832) baseStart_3687832 baseEnd_3687832 := by
    simpa [prefixWord, tailWord_3687832, baseEnd_3687832] using wordTrace_append hprefix tailTrace_3687832
  have hstable : (prefixWord ++ tailWord_3687832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687832).length < 2 ^ (prefixWord ++ tailWord_3687832).sum := by decide
  have hdescent : baseEnd_3687832 < baseStart_3687832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687858 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_3687858 : Nat := 118140960795 + 3687858 * 2 ^ 59
def prefixEnd_3687858 : Nat := 4983230072969 + 3 ^ 40 * 3687858 * 2
def baseEnd_3687858 : Nat := 1262429159685824981543237

theorem tailTrace_3687858 : CollatzResearch.WordTrace tailWord_3687858 prefixEnd_3687858 1262429159685824981543237 := by
  unfold tailWord_3687858
  simp only [CollatzResearch.WordTrace]
  refine ⟨33626807868381944211926057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89671487649018517898469485 33626807868381944211926057)
  ·
    refine ⟨25220105901286458158944543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33626807868381944211926057 25220105901286458158944543)
    ·
      refine ⟨37830158851929687238416815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25220105901286458158944543 37830158851929687238416815)
      ·
        refine ⟨56745238277894530857625223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37830158851929687238416815 56745238277894530857625223)
        ·
          refine ⟨85117857416841796286437835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56745238277894530857625223 85117857416841796286437835)
          ·
            refine ⟨127676786125262694429656753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85117857416841796286437835 127676786125262694429656753)
            ·
              refine ⟨95757589593947020822242565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127676786125262694429656753 95757589593947020822242565)
              ·
                refine ⟨17954548048865066404170481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95757589593947020822242565 17954548048865066404170481)
                ·
                  refine ⟨13465911036648799803127861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17954548048865066404170481 13465911036648799803127861)
                  ·
                    refine ⟨1262429159685824981543237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13465911036648799803127861 1262429159685824981543237)
                    ·
                      rfl

theorem cell22_3687858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_3687858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687858 prefixEnd_3687858 := by exact prefixLift 3687858
  have htrace : WordTrace (prefixWord ++ tailWord_3687858) baseStart_3687858 baseEnd_3687858 := by
    simpa [prefixWord, tailWord_3687858, baseEnd_3687858] using wordTrace_append hprefix tailTrace_3687858
  have hstable : (prefixWord ++ tailWord_3687858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687858).length < 2 ^ (prefixWord ++ tailWord_3687858).sum := by decide
  have hdescent : baseEnd_3687858 < baseStart_3687858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687937 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 1, 5]
def baseStart_3687937 : Nat := 118140960795 + 3687937 * 2 ^ 59
def prefixEnd_3687937 : Nat := 4983230072969 + 3 ^ 40 * 3687937 * 2
def baseEnd_3687937 : Nat := 1262456203000295108817995

theorem tailTrace_3687937 : CollatzResearch.WordTrace tailWord_3687937 prefixEnd_3687937 1262456203000295108817995 := by
  unfold tailWord_3687937
  simp only [CollatzResearch.WordTrace]
  refine ⟨134510112840241573339830065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89673408560161048893220043 134510112840241573339830065)
  ·
    refine ⟨100882584630181180004872549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134510112840241573339830065 100882584630181180004872549)
    ·
      refine ⟨18915484618158971250913603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100882584630181180004872549 18915484618158971250913603)
      ·
        refine ⟨28373226927238456876370405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18915484618158971250913603 28373226927238456876370405)
        ·
          refine ⟨5319980048857210664319451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28373226927238456876370405 5319980048857210664319451)
          ·
            refine ⟨7979970073285815996479177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5319980048857210664319451 7979970073285815996479177)
            ·
              refine ⟨5984977554964361997359383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7979970073285815996479177 5984977554964361997359383)
              ·
                refine ⟨8977466332446542996039075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5984977554964361997359383 8977466332446542996039075)
                ·
                  refine ⟨13466199498669814494058613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8977466332446542996039075 13466199498669814494058613)
                  ·
                    refine ⟨1262456203000295108817995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13466199498669814494058613 1262456203000295108817995)
                    ·
                      rfl

theorem cell22_3687937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_3687937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687937 prefixEnd_3687937 := by exact prefixLift 3687937
  have htrace : WordTrace (prefixWord ++ tailWord_3687937) baseStart_3687937 baseEnd_3687937 := by
    simpa [prefixWord, tailWord_3687937, baseEnd_3687937] using wordTrace_append hprefix tailTrace_3687937
  have hstable : (prefixWord ++ tailWord_3687937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687937).length < 2 ^ (prefixWord ++ tailWord_3687937).sum := by decide
  have hdescent : baseEnd_3687937 < baseStart_3687937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687956 : List Nat := [2, 4, 3, 1, 2, 1, 2, 3, 4]
def baseStart_3687956 : Nat := 118140960795 + 3687956 * 2 ^ 59
def prefixEnd_3687956 : Nat := 4983230072969 + 3 ^ 40 * 3687956 * 2
def baseEnd_3687956 : Nat := 420820902362861797530979

theorem tailTrace_3687956 : CollatzResearch.WordTrace tailWord_3687956 prefixEnd_3687956 420820902362861797530979 := by
  unfold tailWord_3687956
  simp only [CollatzResearch.WordTrace]
  refine ⟨67255402913586369792385861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89673870551448493056514481 67255402913586369792385861)
  ·
    refine ⟨12610388046297444336072349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67255402913586369792385861 12610388046297444336072349)
    ·
      refine ⟨4728895517361541626027131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12610388046297444336072349 4728895517361541626027131)
      ·
        refine ⟨7093343276042312439040697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4728895517361541626027131 7093343276042312439040697)
        ·
          refine ⟨5320007457031734329280523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7093343276042312439040697 5320007457031734329280523)
          ·
            refine ⟨7980011185547601493920785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5320007457031734329280523 7980011185547601493920785)
            ·
              refine ⟨5985008389160701120440589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7980011185547601493920785 5985008389160701120440589)
              ·
                refine ⟨2244378145935262920165221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5985008389160701120440589 2244378145935262920165221)
                ·
                  refine ⟨420820902362861797530979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2244378145935262920165221 420820902362861797530979)
                  ·
                    rfl

theorem cell22_3687956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_3687956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687956 prefixEnd_3687956 := by exact prefixLift 3687956
  have htrace : WordTrace (prefixWord ++ tailWord_3687956) baseStart_3687956 baseEnd_3687956 := by
    simpa [prefixWord, tailWord_3687956, baseEnd_3687956] using wordTrace_append hprefix tailTrace_3687956
  have hstable : (prefixWord ++ tailWord_3687956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687956).length < 2 ^ (prefixWord ++ tailWord_3687956).sum := by decide
  have hdescent : baseEnd_3687956 < baseStart_3687956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3687971 : List Nat := [1, 1, 1, 4, 6, 1, 1, 2, 2, 3]
def baseStart_3687971 : Nat := 118140960795 + 3687971 * 2 ^ 59
def prefixEnd_3687971 : Nat := 4983230072969 + 3 ^ 40 * 3687971 * 2
def baseEnd_3687971 : Nat := 1262467841895130353467891

theorem tailTrace_3687971 : CollatzResearch.WordTrace tailWord_3687971 prefixEnd_3687971 1262467841895130353467891 := by
  unfold tailWord_3687971
  simp only [CollatzResearch.WordTrace]
  refine ⟨134511352922118397146567767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89674235281412264764378511 134511352922118397146567767)
  ·
    refine ⟨201767029383177595719851651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134511352922118397146567767 201767029383177595719851651)
    ·
      refine ⟨302650544074766393579777477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201767029383177595719851651 302650544074766393579777477)
      ·
        refine ⟨56746977014018698796208277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 302650544074766393579777477 56746977014018698796208277)
        ·
          refine ⟨2660014547532126506072263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56746977014018698796208277 2660014547532126506072263)
          ·
            refine ⟨3990021821298189759108395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660014547532126506072263 3990021821298189759108395)
            ·
              refine ⟨5985032731947284638662593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3990021821298189759108395 5985032731947284638662593)
              ·
                refine ⟨4488774548960463478996945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5985032731947284638662593 4488774548960463478996945)
                ·
                  refine ⟨3366580911720347609247709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4488774548960463478996945 3366580911720347609247709)
                  ·
                    refine ⟨1262467841895130353467891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3366580911720347609247709 1262467841895130353467891)
                    ·
                      rfl

theorem cell22_3687971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 2, 3].length) (baseStart_3687971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3687971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3687971 prefixEnd_3687971 := by exact prefixLift 3687971
  have htrace : WordTrace (prefixWord ++ tailWord_3687971) baseStart_3687971 baseEnd_3687971 := by
    simpa [prefixWord, tailWord_3687971, baseEnd_3687971] using wordTrace_append hprefix tailTrace_3687971
  have hstable : (prefixWord ++ tailWord_3687971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3687971).length < 2 ^ (prefixWord ++ tailWord_3687971).sum := by decide
  have hdescent : baseEnd_3687971 < baseStart_3687971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3687971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688046 : List Nat := [4, 1, 2, 2, 3, 2, 2, 1, 5]
def baseStart_3688046 : Nat := 118140960795 + 3688046 * 2 ^ 59
def prefixEnd_3688046 : Nat := 4983230072969 + 3 ^ 40 * 3688046 * 2
def baseEnd_3688046 : Nat := 420831171975951719280887

theorem tailTrace_3688046 : CollatzResearch.WordTrace tailWord_3688046 prefixEnd_3688046 420831171975951719280887 := by
  unfold tailWord_3688046
  simp only [CollatzResearch.WordTrace]
  refine ⟨16814261049605835619443499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89676058931231123303698661 16814261049605835619443499)
  ·
    refine ⟨25221391574408753429165249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16814261049605835619443499 25221391574408753429165249)
    ·
      refine ⟨18916043680806565071873937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25221391574408753429165249 18916043680806565071873937)
      ·
        refine ⟨14187032760604923803905453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18916043680806565071873937 14187032760604923803905453)
        ·
          refine ⟨5320137285226846426464545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14187032760604923803905453 5320137285226846426464545)
          ·
            refine ⟨3990102963920134819848409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5320137285226846426464545 3990102963920134819848409)
            ·
              refine ⟨2992577222940101114886307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3990102963920134819848409 2992577222940101114886307)
              ·
                refine ⟨4488865834410151672329461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2992577222940101114886307 4488865834410151672329461)
                ·
                  refine ⟨420831171975951719280887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4488865834410151672329461 420831171975951719280887)
                  ·
                    rfl

theorem cell22_3688046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_3688046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688046 prefixEnd_3688046 := by exact prefixLift 3688046
  have htrace : WordTrace (prefixWord ++ tailWord_3688046) baseStart_3688046 baseEnd_3688046 := by
    simpa [prefixWord, tailWord_3688046, baseEnd_3688046] using wordTrace_append hprefix tailTrace_3688046
  have hstable : (prefixWord ++ tailWord_3688046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688046).length < 2 ^ (prefixWord ++ tailWord_3688046).sum := by decide
  have hdescent : baseEnd_3688046 < baseStart_3688046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688055 : List Nat := [1, 1, 3, 1, 1, 3, 1, 5, 1, 5]
def baseStart_3688055 : Nat := 118140960795 + 3688055 * 2 ^ 59
def prefixEnd_3688055 : Nat := 4983230072969 + 3 ^ 40 * 3688055 * 2
def baseEnd_3688055 : Nat := 1262496596811782134367633

theorem tailTrace_3688055 : CollatzResearch.WordTrace tailWord_3688055 prefixEnd_3688055 1262496596811782134367633 := by
  unfold tailWord_3688055
  simp only [CollatzResearch.WordTrace]
  refine ⟨134514416653814079492625619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89676277769209386328417079 134514416653814079492625619)
  ·
    refine ⟨201771624980721119238938429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134514416653814079492625619 201771624980721119238938429)
    ·
      refine ⟨75664359367770419714601911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201771624980721119238938429 75664359367770419714601911)
      ·
        refine ⟨113496539051655629571902867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75664359367770419714601911 113496539051655629571902867)
        ·
          refine ⟨170244808577483444357854301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113496539051655629571902867 170244808577483444357854301)
          ·
            refine ⟨63841803216556291634195363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170244808577483444357854301 63841803216556291634195363)
            ·
              refine ⟨95762704824834437451293045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63841803216556291634195363 95762704824834437451293045)
              ·
                refine ⟨8977753577328228511058723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95762704824834437451293045 8977753577328228511058723)
                ·
                  refine ⟨13466630365992342766588085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8977753577328228511058723 13466630365992342766588085)
                  ·
                    refine ⟨1262496596811782134367633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13466630365992342766588085 1262496596811782134367633)
                    ·
                      rfl

theorem cell22_3688055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_3688055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688055 prefixEnd_3688055 := by exact prefixLift 3688055
  have htrace : WordTrace (prefixWord ++ tailWord_3688055) baseStart_3688055 baseEnd_3688055 := by
    simpa [prefixWord, tailWord_3688055, baseEnd_3688055] using wordTrace_append hprefix tailTrace_3688055
  have hstable : (prefixWord ++ tailWord_3688055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688055).length < 2 ^ (prefixWord ++ tailWord_3688055).sum := by decide
  have hdescent : baseEnd_3688055 < baseStart_3688055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688087 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 2, 4]
def baseStart_3688087 : Nat := 118140960795 + 3688087 * 2 ^ 59
def prefixEnd_3688087 : Nat := 4983230072969 + 3 ^ 40 * 3688087 * 2
def baseEnd_3688087 : Nat := 1262507551065744717567535

theorem tailTrace_3688087 : CollatzResearch.WordTrace tailWord_3688087 prefixEnd_3688087 1262507551065744717567535 := by
  unfold tailWord_3688087
  simp only [CollatzResearch.WordTrace]
  refine ⟨134515583789698148957790515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89677055859798765971860343 134515583789698148957790515)
  ·
    refine ⟨201773375684547223436685773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134515583789698148957790515 201773375684547223436685773)
    ·
      refine ⟨75665015881705208788757165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201773375684547223436685773 75665015881705208788757165)
      ·
        refine ⟨28374380955639453295783937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75665015881705208788757165 28374380955639453295783937)
        ·
          refine ⟨21280785716729589971837953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28374380955639453295783937 21280785716729589971837953)
          ·
            refine ⟨15960589287547192478878465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21280785716729589971837953 15960589287547192478878465)
            ·
              refine ⟨11970441965660394359158849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15960589287547192478878465 11970441965660394359158849)
              ·
                refine ⟨8977831474245295769369137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11970441965660394359158849 8977831474245295769369137)
                ·
                  refine ⟨6733373605683971827026853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8977831474245295769369137 6733373605683971827026853)
                  ·
                    refine ⟨1262507551065744717567535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6733373605683971827026853 1262507551065744717567535)
                    ·
                      rfl

theorem cell22_3688087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_3688087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688087 prefixEnd_3688087 := by exact prefixLift 3688087
  have htrace : WordTrace (prefixWord ++ tailWord_3688087) baseStart_3688087 baseEnd_3688087 := by
    simpa [prefixWord, tailWord_3688087, baseEnd_3688087] using wordTrace_append hprefix tailTrace_3688087
  have hstable : (prefixWord ++ tailWord_3688087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688087).length < 2 ^ (prefixWord ++ tailWord_3688087).sum := by decide
  have hdescent : baseEnd_3688087 < baseStart_3688087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688115 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 2, 6]
def baseStart_3688115 : Nat := 118140960795 + 3688115 * 2 ^ 59
def prefixEnd_3688115 : Nat := 4983230072969 + 3 ^ 40 * 3688115 * 2
def baseEnd_3688115 : Nat := 1262517136037961977867449

theorem tailTrace_3688115 : CollatzResearch.WordTrace tailWord_3688115 prefixEnd_3688115 1262517136037961977867449 := by
  unfold tailWord_3688115
  simp only [CollatzResearch.WordTrace]
  refine ⟨134516605033596709739809799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89677736689064473159873199 134516605033596709739809799)
  ·
    refine ⟨201774907550395064609714699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134516605033596709739809799 201774907550395064609714699)
    ·
      refine ⟨302662361325592596914572049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201774907550395064609714699 302662361325592596914572049)
      ·
        refine ⟨226996770994194447685929037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302662361325592596914572049 226996770994194447685929037)
        ·
          refine ⟨85123789122822917882223389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226996770994194447685929037 85123789122822917882223389)
          ·
            refine ⟨31921420921058594205833771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85123789122822917882223389 31921420921058594205833771)
            ·
              refine ⟨47882131381587891308750657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31921420921058594205833771 47882131381587891308750657)
              ·
                refine ⟨35911598536190918481562993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47882131381587891308750657 35911598536190918481562993)
                ·
                  refine ⟨26933698902143188861172245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35911598536190918481562993 26933698902143188861172245)
                  ·
                    refine ⟨1262517136037961977867449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26933698902143188861172245 1262517136037961977867449)
                    ·
                      rfl

theorem cell22_3688115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 6].length) (baseStart_3688115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688115 prefixEnd_3688115 := by exact prefixLift 3688115
  have htrace : WordTrace (prefixWord ++ tailWord_3688115) baseStart_3688115 baseEnd_3688115 := by
    simpa [prefixWord, tailWord_3688115, baseEnd_3688115] using wordTrace_append hprefix tailTrace_3688115
  have hstable : (prefixWord ++ tailWord_3688115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688115).length < 2 ^ (prefixWord ++ tailWord_3688115).sum := by decide
  have hdescent : baseEnd_3688115 < baseStart_3688115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688164 : List Nat := [2, 3, 1, 1, 1, 3, 5, 1, 5]
def baseStart_3688164 : Nat := 118140960795 + 3688164 * 2 ^ 59
def prefixEnd_3688164 : Nat := 4983230072969 + 3 ^ 40 * 3688164 * 2
def baseEnd_3688164 : Nat := 420844636579780727797433

theorem tailTrace_3688164 : CollatzResearch.WordTrace tailWord_3688164 prefixEnd_3688164 420844636579780727797433 := by
  unfold tailWord_3688164
  simp only [CollatzResearch.WordTrace]
  refine ⟨67259196105209595554171773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89678928140279460738895697 67259196105209595554171773)
  ·
    refine ⟨25222198539453598332814415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67259196105209595554171773 25222198539453598332814415)
    ·
      refine ⟨37833297809180397499221623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25222198539453598332814415 37833297809180397499221623)
      ·
        refine ⟨56749946713770596248832435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37833297809180397499221623 56749946713770596248832435)
        ·
          refine ⟨85124920070655894373248653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56749946713770596248832435 85124920070655894373248653)
          ·
            refine ⟨31921845026495960389968245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85124920070655894373248653 31921845026495960389968245)
            ·
              refine ⟨2992672971233996286559523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31921845026495960389968245 2992672971233996286559523)
              ·
                refine ⟨4489009456850994429839285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2992672971233996286559523 4489009456850994429839285)
                ·
                  refine ⟨420844636579780727797433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4489009456850994429839285 420844636579780727797433)
                  ·
                    rfl

theorem cell22_3688164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_3688164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688164 prefixEnd_3688164 := by exact prefixLift 3688164
  have htrace : WordTrace (prefixWord ++ tailWord_3688164) baseStart_3688164 baseEnd_3688164 := by
    simpa [prefixWord, tailWord_3688164, baseEnd_3688164] using wordTrace_append hprefix tailTrace_3688164
  have hstable : (prefixWord ++ tailWord_3688164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688164).length < 2 ^ (prefixWord ++ tailWord_3688164).sum := by decide
  have hdescent : baseEnd_3688164 < baseStart_3688164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688346 : List Nat := [3, 1, 1, 4, 2, 1, 1, 4, 1, 4]
def baseStart_3688346 : Nat := 118140960795 + 3688346 * 2 ^ 59
def prefixEnd_3688346 : Nat := 4983230072969 + 3 ^ 40 * 3688346 * 2
def baseEnd_3688346 : Nat := 1262596212058754375341741

theorem tailTrace_3688346 : CollatzResearch.WordTrace tailWord_3688346 prefixEnd_3688346 1262596212058754375341741 := by
  unfold tailWord_3688346
  simp only [CollatzResearch.WordTrace]
  refine ⟨33631257573939959047867223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89683353530506557460979261 33631257573939959047867223)
  ·
    refine ⟨50446886360909938571800835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33631257573939959047867223 50446886360909938571800835)
    ·
      refine ⟨75670329541364907857701253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50446886360909938571800835 75670329541364907857701253)
      ·
        refine ⟨14188186789005920223318985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75670329541364907857701253 14188186789005920223318985)
        ·
          refine ⟨10641140091754440167489239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14188186789005920223318985 10641140091754440167489239)
          ·
            refine ⟨15961710137631660251233859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10641140091754440167489239 15961710137631660251233859)
            ·
              refine ⟨23942565206447490376850789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15961710137631660251233859 23942565206447490376850789)
              ·
                refine ⟨4489230976208904445659523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23942565206447490376850789 4489230976208904445659523)
                ·
                  refine ⟨6733846464313356668489285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4489230976208904445659523 6733846464313356668489285)
                  ·
                    refine ⟨1262596212058754375341741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6733846464313356668489285 1262596212058754375341741)
                    ·
                      rfl

theorem cell22_3688346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 4, 1, 4].length) (baseStart_3688346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688346 prefixEnd_3688346 := by exact prefixLift 3688346
  have htrace : WordTrace (prefixWord ++ tailWord_3688346) baseStart_3688346 baseEnd_3688346 := by
    simpa [prefixWord, tailWord_3688346, baseEnd_3688346] using wordTrace_append hprefix tailTrace_3688346
  have hstable : (prefixWord ++ tailWord_3688346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688346).length < 2 ^ (prefixWord ++ tailWord_3688346).sum := by decide
  have hdescent : baseEnd_3688346 < baseStart_3688346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688376 : List Nat := [2, 1, 2, 1, 2, 3, 2, 4, 2, 3]
def baseStart_3688376 : Nat := 118140960795 + 3688376 * 2 ^ 59
def prefixEnd_3688376 : Nat := 4983230072969 + 3 ^ 40 * 3688376 * 2
def baseEnd_3688376 : Nat := 1262606481671844297091649

theorem tailTrace_3688376 : CollatzResearch.WordTrace tailWord_3688376 prefixEnd_3688376 1262606481671844297091649 := by
  unfold tailWord_3688376
  simp only [CollatzResearch.WordTrace]
  refine ⟨67263062242825575657530491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89684082990434100876707321 67263062242825575657530491)
  ·
    refine ⟨100894593364238363486295737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67263062242825575657530491 100894593364238363486295737)
    ·
      refine ⟨75670945023178772614721803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100894593364238363486295737 75670945023178772614721803)
      ·
        refine ⟨113506417534768158922082705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75670945023178772614721803 113506417534768158922082705)
        ·
          refine ⟨85129813151076119191562029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113506417534768158922082705 85129813151076119191562029)
          ·
            refine ⟨31923679931653544696835761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85129813151076119191562029 31923679931653544696835761)
            ·
              refine ⟨23942759948740158522626821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31923679931653544696835761 23942759948740158522626821)
              ·
                refine ⟨4489267490388779722992529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23942759948740158522626821 4489267490388779722992529)
                ·
                  refine ⟨3366950617791584792244397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4489267490388779722992529 3366950617791584792244397)
                  ·
                    refine ⟨1262606481671844297091649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3366950617791584792244397 1262606481671844297091649)
                    ·
                      rfl

theorem cell22_3688376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 4, 2, 3].length) (baseStart_3688376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688376 prefixEnd_3688376 := by exact prefixLift 3688376
  have htrace : WordTrace (prefixWord ++ tailWord_3688376) baseStart_3688376 baseEnd_3688376 := by
    simpa [prefixWord, tailWord_3688376, baseEnd_3688376] using wordTrace_append hprefix tailTrace_3688376
  have hstable : (prefixWord ++ tailWord_3688376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688376).length < 2 ^ (prefixWord ++ tailWord_3688376).sum := by decide
  have hdescent : baseEnd_3688376 < baseStart_3688376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688429 : List Nat := [1, 5, 1, 4, 2, 1, 2, 2, 4]
def baseStart_3688429 : Nat := 118140960795 + 3688429 * 2 ^ 59
def prefixEnd_3688429 : Nat := 4983230072969 + 3 ^ 40 * 3688429 * 2
def baseEnd_3688429 : Nat := 420874874884989941838829

theorem tailTrace_3688429 : CollatzResearch.WordTrace tailWord_3688429 prefixEnd_3688429 420874874884989941838829 := by
  unfold tailWord_3688429
  simp only [CollatzResearch.WordTrace]
  refine ⟨134528057554459141366740341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89685371702972760911160227 134528057554459141366740341)
  ·
    refine ⟨12612005395730544503131907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134528057554459141366740341 12612005395730544503131907)
    ·
      refine ⟨18918008093595816754697861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12612005395730544503131907 18918008093595816754697861)
      ·
        refine ⟨3547126517549215641505849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18918008093595816754697861 3547126517549215641505849)
        ·
          refine ⟨2660344888161911731129387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3547126517549215641505849 2660344888161911731129387)
          ·
            refine ⟨3990517332242867596694081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660344888161911731129387 3990517332242867596694081)
            ·
              refine ⟨2992887999182150697520561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3990517332242867596694081 2992887999182150697520561)
              ·
                refine ⟨2244665999386613023140421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2992887999182150697520561 2244665999386613023140421)
                ·
                  refine ⟨420874874884989941838829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2244665999386613023140421 420874874884989941838829)
                  ·
                    rfl

theorem cell22_3688429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_3688429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688429 prefixEnd_3688429 := by exact prefixLift 3688429
  have htrace : WordTrace (prefixWord ++ tailWord_3688429) baseStart_3688429 baseEnd_3688429 := by
    simpa [prefixWord, tailWord_3688429, baseEnd_3688429] using wordTrace_append hprefix tailTrace_3688429
  have hstable : (prefixWord ++ tailWord_3688429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688429).length < 2 ^ (prefixWord ++ tailWord_3688429).sum := by decide
  have hdescent : baseEnd_3688429 < baseStart_3688429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688479 : List Nat := [1, 1, 2, 4, 1, 2, 1, 2, 8]
def baseStart_3688479 : Nat := 118140960795 + 3688479 * 2 ^ 59
def prefixEnd_3688479 : Nat := 4983230072969 + 3 ^ 40 * 3688479 * 2
def baseEnd_3688479 : Nat := 420880580225595453922111

theorem tailTrace_3688479 : CollatzResearch.WordTrace tailWord_3688479 prefixEnd_3688479 420880580225595453922111 := by
  unfold tailWord_3688479
  simp only [CollatzResearch.WordTrace]
  refine ⟨134529881204277999906060491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89686587469518666604040327 134529881204277999906060491)
  ·
    refine ⟨201794821806416999859090737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134529881204277999906060491 201794821806416999859090737)
    ·
      refine ⟨151346116354812749894318053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201794821806416999859090737 151346116354812749894318053)
      ·
        refine ⟨28377396816527390605184635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151346116354812749894318053 28377396816527390605184635)
        ·
          refine ⟨42566095224791085907776953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28377396816527390605184635 42566095224791085907776953)
          ·
            refine ⟨31924571418593314430832715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42566095224791085907776953 31924571418593314430832715)
            ·
              refine ⟨47886857127889971646249073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31924571418593314430832715 47886857127889971646249073)
              ·
                refine ⟨35915142845917478734686805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47886857127889971646249073 35915142845917478734686805)
                ·
                  refine ⟨420880580225595453922111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35915142845917478734686805 420880580225595453922111)
                  ·
                    rfl

theorem cell22_3688479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 2, 8].length) (baseStart_3688479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688479 prefixEnd_3688479 := by exact prefixLift 3688479
  have htrace : WordTrace (prefixWord ++ tailWord_3688479) baseStart_3688479 baseEnd_3688479 := by
    simpa [prefixWord, tailWord_3688479, baseEnd_3688479] using wordTrace_append hprefix tailTrace_3688479
  have hstable : (prefixWord ++ tailWord_3688479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688479).length < 2 ^ (prefixWord ++ tailWord_3688479).sum := by decide
  have hdescent : baseEnd_3688479 < baseStart_3688479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688496 : List Nat := [2, 1, 1, 1, 2, 6, 2, 1, 6]
def baseStart_3688496 : Nat := 118140960795 + 3688496 * 2 ^ 59
def prefixEnd_3688496 : Nat := 4983230072969 + 3 ^ 40 * 3688496 * 2
def baseEnd_3688496 : Nat := 420882520041401328030427

theorem tailTrace_3688496 : CollatzResearch.WordTrace tailWord_3688496 prefixEnd_3688496 420882520041401328030427 := by
  unfold tailWord_3688496
  simp only [CollatzResearch.WordTrace]
  refine ⟨67265250622608205904714671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89687000830144274539619561 67265250622608205904714671)
  ·
    refine ⟨100897875933912308857072007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67265250622608205904714671 100897875933912308857072007)
    ·
      refine ⟨151346813900868463285608011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100897875933912308857072007 151346813900868463285608011)
      ·
        refine ⟨227020220851302694928412017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151346813900868463285608011 227020220851302694928412017)
        ·
          refine ⟨170265165638477021196309013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227020220851302694928412017 170265165638477021196309013)
          ·
            refine ⟨7981179639303610368576985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 170265165638477021196309013 7981179639303610368576985)
            ·
              refine ⟨5985884729477707776432739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7981179639303610368576985 5985884729477707776432739)
              ·
                refine ⟨8978827094216561664649109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5985884729477707776432739 8978827094216561664649109)
                ·
                  refine ⟨420882520041401328030427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8978827094216561664649109 420882520041401328030427)
                  ·
                    rfl

theorem cell22_3688496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 1, 6].length) (baseStart_3688496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688496 prefixEnd_3688496 := by exact prefixLift 3688496
  have htrace : WordTrace (prefixWord ++ tailWord_3688496) baseStart_3688496 baseEnd_3688496 := by
    simpa [prefixWord, tailWord_3688496, baseEnd_3688496] using wordTrace_append hprefix tailTrace_3688496
  have hstable : (prefixWord ++ tailWord_3688496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688496).length < 2 ^ (prefixWord ++ tailWord_3688496).sum := by decide
  have hdescent : baseEnd_3688496 < baseStart_3688496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688511 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 1, 5]
def baseStart_3688511 : Nat := 118140960795 + 3688511 * 2 ^ 59
def prefixEnd_3688511 : Nat := 4983230072969 + 3 ^ 40 * 3688511 * 2
def baseEnd_3688511 : Nat := 1262652694930748944966235

theorem tailTrace_3688511 : CollatzResearch.WordTrace tailWord_3688511 prefixEnd_3688511 1262652694930748944966235 := by
  unfold tailWord_3688511
  simp only [CollatzResearch.WordTrace]
  refine ⟨134531048340162069371225387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89687365560108046247483591 134531048340162069371225387)
  ·
    refine ⟨201796572510243104056838081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134531048340162069371225387 201796572510243104056838081)
    ·
      refine ⟨151347429382682328042628561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201796572510243104056838081 151347429382682328042628561)
      ·
        refine ⟨113510572037011746031971421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151347429382682328042628561 113510572037011746031971421)
        ·
          refine ⟨42566464513879404761989283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113510572037011746031971421 42566464513879404761989283)
          ·
            refine ⟨63849696770819107142983925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42566464513879404761989283 63849696770819107142983925)
            ·
              refine ⟨5985909072264291294654743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63849696770819107142983925 5985909072264291294654743)
              ·
                refine ⟨8978863608396436941982115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5985909072264291294654743 8978863608396436941982115)
                ·
                  refine ⟨13468295412594655412973173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8978863608396436941982115 13468295412594655412973173)
                  ·
                    refine ⟨1262652694930748944966235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13468295412594655412973173 1262652694930748944966235)
                    ·
                      rfl

theorem cell22_3688511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_3688511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688511 prefixEnd_3688511 := by exact prefixLift 3688511
  have htrace : WordTrace (prefixWord ++ tailWord_3688511) baseStart_3688511 baseEnd_3688511 := by
    simpa [prefixWord, tailWord_3688511, baseEnd_3688511] using wordTrace_append hprefix tailTrace_3688511
  have hstable : (prefixWord ++ tailWord_3688511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688511).length < 2 ^ (prefixWord ++ tailWord_3688511).sum := by decide
  have hdescent : baseEnd_3688511 < baseStart_3688511 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688526 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_3688526 : Nat := 118140960795 + 3688526 * 2 ^ 59
def prefixEnd_3688526 : Nat := 4983230072969 + 3 ^ 40 * 3688526 * 2
def baseEnd_3688526 : Nat := 1262657829737293905841189

theorem tailTrace_3688526 : CollatzResearch.WordTrace tailWord_3688526 prefixEnd_3688526 1262657829737293905841189 := by
  unfold tailWord_3688526
  simp only [CollatzResearch.WordTrace]
  refine ⟨16816449429388465866627679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89687730290071817955347621 16816449429388465866627679)
  ·
    refine ⟨25224674144082698799941519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16816449429388465866627679 25224674144082698799941519)
    ·
      refine ⟨37837011216124048199912279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25224674144082698799941519 37837011216124048199912279)
      ·
        refine ⟨56755516824186072299868419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37837011216124048199912279 56755516824186072299868419)
        ·
          refine ⟨85133275236279108449802629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56755516824186072299868419 85133275236279108449802629)
          ·
            refine ⟨15962489106802332834337993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85133275236279108449802629 15962489106802332834337993)
            ·
              refine ⟨11971866830101749625753495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15962489106802332834337993 11971866830101749625753495)
              ·
                refine ⟨17957800245152624438630243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11971866830101749625753495 17957800245152624438630243)
                ·
                  refine ⟨26936700367728936657945365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17957800245152624438630243 26936700367728936657945365)
                  ·
                    refine ⟨1262657829737293905841189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26936700367728936657945365 1262657829737293905841189)
                    ·
                      rfl

theorem cell22_3688526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_3688526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688526 prefixEnd_3688526 := by exact prefixLift 3688526
  have htrace : WordTrace (prefixWord ++ tailWord_3688526) baseStart_3688526 baseEnd_3688526 := by
    simpa [prefixWord, tailWord_3688526, baseEnd_3688526] using wordTrace_append hprefix tailTrace_3688526
  have hstable : (prefixWord ++ tailWord_3688526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688526).length < 2 ^ (prefixWord ++ tailWord_3688526).sum := by decide
  have hdescent : baseEnd_3688526 < baseStart_3688526 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688562 : List Nat := [3, 2, 1, 2, 2, 4, 2, 1, 2, 3]
def baseStart_3688562 : Nat := 118140960795 + 3688562 * 2 ^ 59
def prefixEnd_3688562 : Nat := 4983230072969 + 3 ^ 40 * 3688562 * 2
def baseEnd_3688562 : Nat := 1262670153273001811941079

theorem tailTrace_3688562 : CollatzResearch.WordTrace tailWord_3688562 prefixEnd_3688562 1262670153273001811941079 := by
  unfold tailWord_3688562
  simp only [CollatzResearch.WordTrace]
  refine ⟨33633227115744326270332985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89688605641984870054221293 33633227115744326270332985)
  ·
    refine ⟨25224920336808244702749739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33633227115744326270332985 25224920336808244702749739)
    ·
      refine ⟨37837380505212367054124609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25224920336808244702749739 37837380505212367054124609)
      ·
        refine ⟨28378035378909275290593457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37837380505212367054124609 28378035378909275290593457)
        ·
          refine ⟨21283526534181956467945093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28378035378909275290593457 21283526534181956467945093)
          ·
            refine ⟨3990661225159116837739705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21283526534181956467945093 3990661225159116837739705)
            ·
              refine ⟨2992995918869337628304779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3990661225159116837739705 2992995918869337628304779)
              ·
                refine ⟨4489493878304006442457169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2992995918869337628304779 4489493878304006442457169)
                ·
                  refine ⟨3367120408728004831842877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4489493878304006442457169 3367120408728004831842877)
                  ·
                    refine ⟨1262670153273001811941079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3367120408728004831842877 1262670153273001811941079)
                    ·
                      rfl

theorem cell22_3688562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_3688562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688562 prefixEnd_3688562 := by exact prefixLift 3688562
  have htrace : WordTrace (prefixWord ++ tailWord_3688562) baseStart_3688562 baseEnd_3688562 := by
    simpa [prefixWord, tailWord_3688562, baseEnd_3688562] using wordTrace_append hprefix tailTrace_3688562
  have hstable : (prefixWord ++ tailWord_3688562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688562).length < 2 ^ (prefixWord ++ tailWord_3688562).sum := by decide
  have hdescent : baseEnd_3688562 < baseStart_3688562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688607 : List Nat := [1, 1, 2, 6, 1, 2, 1, 4, 1, 3]
def baseStart_3688607 : Nat := 118140960795 + 3688607 * 2 ^ 59
def prefixEnd_3688607 : Nat := 4983230072969 + 3 ^ 40 * 3688607 * 2
def baseEnd_3688607 : Nat := 1262685557692636694565941

theorem tailTrace_3688607 : CollatzResearch.WordTrace tailWord_3688607 prefixEnd_3688607 1262685557692636694565941 := by
  unfold tailWord_3688607
  simp only [CollatzResearch.WordTrace]
  refine ⟨134534549747814277766720075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89689699831876185177813383 134534549747814277766720075)
  ·
    refine ⟨201801824621721416650080113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134534549747814277766720075 201801824621721416650080113)
    ·
      refine ⟨151351368466291062487560085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201801824621721416650080113 151351368466291062487560085)
      ·
        refine ⟨7094595396857393554104379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151351368466291062487560085 7094595396857393554104379)
        ·
          refine ⟨10641893095286090331156569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7094595396857393554104379 10641893095286090331156569)
          ·
            refine ⟨7981419821464567748367427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10641893095286090331156569 7981419821464567748367427)
            ·
              refine ⟨11972129732196851622551141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7981419821464567748367427 11972129732196851622551141)
              ·
                refine ⟨2244774324786909679228339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11972129732196851622551141 2244774324786909679228339)
                ·
                  refine ⟨3367161487180364518842509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2244774324786909679228339 3367161487180364518842509)
                  ·
                    refine ⟨1262685557692636694565941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3367161487180364518842509 1262685557692636694565941)
                    ·
                      rfl

theorem cell22_3688607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 4, 1, 3].length) (baseStart_3688607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688607 prefixEnd_3688607 := by exact prefixLift 3688607
  have htrace : WordTrace (prefixWord ++ tailWord_3688607) baseStart_3688607 baseEnd_3688607 := by
    simpa [prefixWord, tailWord_3688607, baseEnd_3688607] using wordTrace_append hprefix tailTrace_3688607
  have hstable : (prefixWord ++ tailWord_3688607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688607).length < 2 ^ (prefixWord ++ tailWord_3688607).sum := by decide
  have hdescent : baseEnd_3688607 < baseStart_3688607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688631 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 8]
def baseStart_3688631 : Nat := 118140960795 + 3688631 * 2 ^ 59
def prefixEnd_3688631 : Nat := 4983230072969 + 3 ^ 40 * 3688631 * 2
def baseEnd_3688631 : Nat := 420897924461036210655289

theorem tailTrace_3688631 : CollatzResearch.WordTrace tailWord_3688631 prefixEnd_3688631 420897924461036210655289 := by
  unfold tailWord_3688631
  simp only [CollatzResearch.WordTrace]
  refine ⟨134535425099727329865593747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89690283399818219910395831 134535425099727329865593747)
  ·
    refine ⟨201803137649590994798390621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134535425099727329865593747 201803137649590994798390621)
    ·
      refine ⟨75676176618596623049396483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201803137649590994798390621 75676176618596623049396483)
      ·
        refine ⟨113514264927894934574094725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75676176618596623049396483 113514264927894934574094725)
        ·
          refine ⟨21283924673980300232642761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113514264927894934574094725 21283924673980300232642761)
          ·
            refine ⟨15962943505485225174482071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21283924673980300232642761 15962943505485225174482071)
            ·
              refine ⟨23944415258227837761723107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15962943505485225174482071 23944415258227837761723107)
              ·
                refine ⟨35916622887341756642584661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23944415258227837761723107 35916622887341756642584661)
                ·
                  refine ⟨420897924461036210655289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35916622887341756642584661 420897924461036210655289)
                  ·
                    rfl

theorem cell22_3688631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 8].length) (baseStart_3688631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688631 prefixEnd_3688631 := by exact prefixLift 3688631
  have htrace : WordTrace (prefixWord ++ tailWord_3688631) baseStart_3688631 baseEnd_3688631 := by
    simpa [prefixWord, tailWord_3688631, baseEnd_3688631] using wordTrace_append hprefix tailTrace_3688631
  have hstable : (prefixWord ++ tailWord_3688631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688631).length < 2 ^ (prefixWord ++ tailWord_3688631).sum := by decide
  have hdescent : baseEnd_3688631 < baseStart_3688631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688633 : List Nat := [1, 2, 1, 4, 1, 2, 2, 4, 1, 4]
def baseStart_3688633 : Nat := 118140960795 + 3688633 * 2 ^ 59
def prefixEnd_3688633 : Nat := 4983230072969 + 3 ^ 40 * 3688633 * 2
def baseEnd_3688633 : Nat := 1262694458023981293415861

theorem tailTrace_3688633 : CollatzResearch.WordTrace tailWord_3688633 prefixEnd_3688633 1262694458023981293415861 := by
  unfold tailWord_3688633
  simp only [CollatzResearch.WordTrace]
  refine ⟨134535498045720084207166553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89690332030480056138111035 134535498045720084207166553)
  ·
    refine ⟨100901623534290063155374915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134535498045720084207166553 100901623534290063155374915)
    ·
      refine ⟨151352435301435094733062373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100901623534290063155374915 151352435301435094733062373)
      ·
        refine ⟨28378581619019080262449195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151352435301435094733062373 28378581619019080262449195)
        ·
          refine ⟨42567872428528620393673793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28378581619019080262449195 42567872428528620393673793)
          ·
            refine ⟨31925904321396465295255345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42567872428528620393673793 31925904321396465295255345)
            ·
              refine ⟨23944428241047348971441509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31925904321396465295255345 23944428241047348971441509)
              ·
                refine ⟨4489580295196377932145283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23944428241047348971441509 4489580295196377932145283)
                ·
                  refine ⟨6734370442794566898217925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4489580295196377932145283 6734370442794566898217925)
                  ·
                    refine ⟨1262694458023981293415861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6734370442794566898217925 1262694458023981293415861)
                    ·
                      rfl

theorem cell22_3688633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 4].length) (baseStart_3688633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688633 prefixEnd_3688633 := by exact prefixLift 3688633
  have htrace : WordTrace (prefixWord ++ tailWord_3688633) baseStart_3688633 baseEnd_3688633 := by
    simpa [prefixWord, tailWord_3688633, baseEnd_3688633] using wordTrace_append hprefix tailTrace_3688633
  have hstable : (prefixWord ++ tailWord_3688633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688633).length < 2 ^ (prefixWord ++ tailWord_3688633).sum := by decide
  have hdescent : baseEnd_3688633 < baseStart_3688633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688676 : List Nat := [2, 3, 1, 1, 1, 2, 1, 11]
def baseStart_3688676 : Nat := 118140960795 + 3688676 * 2 ^ 59
def prefixEnd_3688676 : Nat := 4983230072969 + 3 ^ 40 * 3688676 * 2
def baseEnd_3688676 : Nat := 140301019755860390510081

theorem tailTrace_3688676 : CollatzResearch.WordTrace tailWord_3688676 prefixEnd_3688676 140301019755860390510081 := by
  unfold tailWord_3688676
  simp only [CollatzResearch.WordTrace]
  refine ⟨67268533192282151275490941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89691377589709535033987921 67268533192282151275490941)
  ·
    refine ⟨25225699947105806728309103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67268533192282151275490941 25225699947105806728309103)
    ·
      refine ⟨37838549920658710092463655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25225699947105806728309103 37838549920658710092463655)
      ·
        refine ⟨56757824880988065138695483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37838549920658710092463655 56757824880988065138695483)
        ·
          refine ⟨85136737321482097708043225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56757824880988065138695483 85136737321482097708043225)
          ·
            refine ⟨63852552991111573281032419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85136737321482097708043225 63852552991111573281032419)
            ·
              refine ⟨95778829486667359921548629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63852552991111573281032419 95778829486667359921548629)
              ·
                refine ⟨140301019755860390510081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 95778829486667359921548629 140301019755860390510081)
                ·
                  rfl

theorem cell22_3688676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 11].length) (baseStart_3688676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688676 prefixEnd_3688676 := by exact prefixLift 3688676
  have htrace : WordTrace (prefixWord ++ tailWord_3688676) baseStart_3688676 baseEnd_3688676 := by
    simpa [prefixWord, tailWord_3688676, baseEnd_3688676] using wordTrace_append hprefix tailTrace_3688676
  have hstable : (prefixWord ++ tailWord_3688676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688676).length < 2 ^ (prefixWord ++ tailWord_3688676).sum := by decide
  have hdescent : baseEnd_3688676 < baseStart_3688676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688680 : List Nat := [2, 1, 4, 1, 2, 4, 1, 1, 1, 5]
def baseStart_3688680 : Nat := 118140960795 + 3688680 * 2 ^ 59
def prefixEnd_3688680 : Nat := 4983230072969 + 3 ^ 40 * 3688680 * 2
def baseEnd_3688680 : Nat := 1262710547084488837490717

theorem tailTrace_3688680 : CollatzResearch.WordTrace tailWord_3688680 prefixEnd_3688680 1262710547084488837490717 := by
  unfold tailWord_3688680
  simp only [CollatzResearch.WordTrace]
  refine ⟨67268606138274905617063747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89691474851033207489418329 67268606138274905617063747)
  ·
    refine ⟨100902909207412358425595621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67268606138274905617063747 100902909207412358425595621)
    ·
      refine ⟨18919295476389817204799179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100902909207412358425595621 18919295476389817204799179)
      ·
        refine ⟨28378943214584725807198769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18919295476389817204799179 28378943214584725807198769)
        ·
          refine ⟨21284207410938544355399077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28378943214584725807198769 21284207410938544355399077)
          ·
            refine ⟨3990788889550977066637327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21284207410938544355399077 3990788889550977066637327)
            ·
              refine ⟨5986183334326465599955991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3990788889550977066637327 5986183334326465599955991)
              ·
                refine ⟨8979275001489698399933987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5986183334326465599955991 8979275001489698399933987)
                ·
                  refine ⟨13468912502234547599900981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8979275001489698399933987 13468912502234547599900981)
                  ·
                    refine ⟨1262710547084488837490717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13468912502234547599900981 1262710547084488837490717)
                    ·
                      rfl

theorem cell22_3688680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_3688680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688680 prefixEnd_3688680 := by exact prefixLift 3688680
  have htrace : WordTrace (prefixWord ++ tailWord_3688680) baseStart_3688680 baseEnd_3688680 := by
    simpa [prefixWord, tailWord_3688680, baseEnd_3688680] using wordTrace_append hprefix tailTrace_3688680
  have hstable : (prefixWord ++ tailWord_3688680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688680).length < 2 ^ (prefixWord ++ tailWord_3688680).sum := by decide
  have hdescent : baseEnd_3688680 < baseStart_3688680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688691 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 2, 7]
def baseStart_3688691 : Nat := 118140960795 + 3688691 * 2 ^ 59
def prefixEnd_3688691 : Nat := 4983230072969 + 3 ^ 40 * 3688691 * 2
def baseEnd_3688691 : Nat := 1262714312609288475465683

theorem tailTrace_3688691 : CollatzResearch.WordTrace tailWord_3688691 prefixEnd_3688691 1262714312609288475465683 := by
  unfold tailWord_3688691
  simp only [CollatzResearch.WordTrace]
  refine ⟨134537613479509960112777927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89691742319673306741851951 134537613479509960112777927)
  ·
    refine ⟨201806420219264940169166891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134537613479509960112777927 201806420219264940169166891)
    ·
      refine ⟨302709630328897410253750337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201806420219264940169166891 302709630328897410253750337)
      ·
        refine ⟨227032222746673057690312753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302709630328897410253750337 227032222746673057690312753)
        ·
          refine ⟨170274167060004793267734565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227032222746673057690312753 170274167060004793267734565)
          ·
            refine ⟨31926406323750898737700231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170274167060004793267734565 31926406323750898737700231)
            ·
              refine ⟨47889609485626348106550347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31926406323750898737700231 47889609485626348106550347)
              ·
                refine ⟨71834414228439522159825521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47889609485626348106550347 71834414228439522159825521)
                ·
                  refine ⟨53875810671329641619869141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71834414228439522159825521 53875810671329641619869141)
                  ·
                    refine ⟨1262714312609288475465683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53875810671329641619869141 1262714312609288475465683)
                    ·
                      rfl

theorem cell22_3688691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 7].length) (baseStart_3688691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688691 prefixEnd_3688691 := by exact prefixLift 3688691
  have htrace : WordTrace (prefixWord ++ tailWord_3688691) baseStart_3688691 baseEnd_3688691 := by
    simpa [prefixWord, tailWord_3688691, baseEnd_3688691] using wordTrace_append hprefix tailTrace_3688691
  have hstable : (prefixWord ++ tailWord_3688691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688691).length < 2 ^ (prefixWord ++ tailWord_3688691).sum := by decide
  have hdescent : baseEnd_3688691 < baseStart_3688691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688725 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 3, 3]
def baseStart_3688725 : Nat := 118140960795 + 3688725 * 2 ^ 59
def prefixEnd_3688725 : Nat := 4983230072969 + 3 ^ 40 * 3688725 * 2
def baseEnd_3688725 : Nat := 1262725951504123720115579

theorem tailTrace_3688725 : CollatzResearch.WordTrace tailWord_3688725 prefixEnd_3688725 1262725951504123720115579 := by
  unfold tailWord_3688725
  simp only [CollatzResearch.WordTrace]
  refine ⟨134538853561386783919515629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89692569040924522613010419 134538853561386783919515629)
  ·
    refine ⟨50452070085520043969818361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134538853561386783919515629 50452070085520043969818361)
    ·
      refine ⟨37839052564140032977363771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50452070085520043969818361 37839052564140032977363771)
      ·
        refine ⟨56758578846210049466045657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37839052564140032977363771 56758578846210049466045657)
        ·
          refine ⟨42568934134657537099534243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56758578846210049466045657 42568934134657537099534243)
          ·
            refine ⟨63853401201986305649301365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42568934134657537099534243 63853401201986305649301365)
            ·
              refine ⟨5986256362686216154622003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63853401201986305649301365 5986256362686216154622003)
              ·
                refine ⟨8979384544029324231933005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5986256362686216154622003 8979384544029324231933005)
                ·
                  refine ⟨3367269204010996586974877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8979384544029324231933005 3367269204010996586974877)
                  ·
                    refine ⟨1262725951504123720115579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3367269204010996586974877 1262725951504123720115579)
                    ·
                      rfl

theorem cell22_3688725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_3688725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688725 prefixEnd_3688725 := by exact prefixLift 3688725
  have htrace : WordTrace (prefixWord ++ tailWord_3688725) baseStart_3688725 baseEnd_3688725 := by
    simpa [prefixWord, tailWord_3688725, baseEnd_3688725] using wordTrace_append hprefix tailTrace_3688725
  have hstable : (prefixWord ++ tailWord_3688725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688725).length < 2 ^ (prefixWord ++ tailWord_3688725).sum := by decide
  have hdescent : baseEnd_3688725 < baseStart_3688725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688800 : List Nat := [2, 1, 1, 3, 5, 1, 1, 2, 6]
def baseStart_3688800 : Nat := 118140960795 + 3688800 * 2 ^ 59
def prefixEnd_3688800 : Nat := 4983230072969 + 3 ^ 40 * 3688800 * 2
def baseEnd_3688800 : Nat := 420917208512282841496783

theorem tailTrace_3688800 : CollatzResearch.WordTrace tailWord_3688800 prefixEnd_3688800 420917208512282841496783 := by
  unfold tailWord_3688800
  simp only [CollatzResearch.WordTrace]
  refine ⟨67270794518057535864247927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89694392690743381152330569 67270794518057535864247927)
  ·
    refine ⟨100906191777086303796371891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67270794518057535864247927 100906191777086303796371891)
    ·
      refine ⟨151359287665629455694557837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100906191777086303796371891 151359287665629455694557837)
      ·
        refine ⟨56759732874611045885459189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151359287665629455694557837 56759732874611045885459189)
        ·
          refine ⟨5321224956994785551761799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56759732874611045885459189 5321224956994785551761799)
          ·
            refine ⟨7981837435492178327642699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5321224956994785551761799 7981837435492178327642699)
            ·
              refine ⟨11972756153238267491464049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7981837435492178327642699 11972756153238267491464049)
              ·
                refine ⟨8979567114928700618598037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11972756153238267491464049 8979567114928700618598037)
                ·
                  refine ⟨420917208512282841496783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8979567114928700618598037 420917208512282841496783)
                  ·
                    rfl

theorem cell22_3688800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 2, 6].length) (baseStart_3688800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688800 prefixEnd_3688800 := by exact prefixLift 3688800
  have htrace : WordTrace (prefixWord ++ tailWord_3688800) baseStart_3688800 baseEnd_3688800 := by
    simpa [prefixWord, tailWord_3688800, baseEnd_3688800] using wordTrace_append hprefix tailTrace_3688800
  have hstable : (prefixWord ++ tailWord_3688800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688800).length < 2 ^ (prefixWord ++ tailWord_3688800).sum := by decide
  have hdescent : baseEnd_3688800 < baseStart_3688800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688834 : List Nat := [3, 4, 2, 1, 2, 1, 2, 1, 6]
def baseStart_3688834 : Nat := 118140960795 + 3688834 * 2 ^ 59
def prefixEnd_3688834 : Nat := 4983230072969 + 3 ^ 40 * 3688834 * 2
def baseEnd_3688834 : Nat := 420921088143894589713415

theorem tailTrace_3688834 : CollatzResearch.WordTrace tailWord_3688834 prefixEnd_3688834 420921088143894589713415 := by
  unfold tailWord_3688834
  simp only [CollatzResearch.WordTrace]
  refine ⟨33635707279497973883808389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89695219411994597023489037 33635707279497973883808389)
  ·
    refine ⟨6306695114905870103214073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33635707279497973883808389 6306695114905870103214073)
    ·
      refine ⟨4730021336179402577410555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6306695114905870103214073 4730021336179402577410555)
      ·
        refine ⟨7095032004269103866115833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4730021336179402577410555 7095032004269103866115833)
        ·
          refine ⟨5321274003201827899586875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7095032004269103866115833 5321274003201827899586875)
          ·
            refine ⟨7981911004802741849380313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5321274003201827899586875 7981911004802741849380313)
            ·
              refine ⟨5986433253602056387035235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7981911004802741849380313 5986433253602056387035235)
              ·
                refine ⟨8979649880403084580552853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5986433253602056387035235 8979649880403084580552853)
                ·
                  refine ⟨420921088143894589713415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8979649880403084580552853 420921088143894589713415)
                  ·
                    rfl

theorem cell22_3688834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_3688834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688834 prefixEnd_3688834 := by exact prefixLift 3688834
  have htrace : WordTrace (prefixWord ++ tailWord_3688834) baseStart_3688834 baseEnd_3688834 := by
    simpa [prefixWord, tailWord_3688834, baseEnd_3688834] using wordTrace_append hprefix tailTrace_3688834
  have hstable : (prefixWord ++ tailWord_3688834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688834).length < 2 ^ (prefixWord ++ tailWord_3688834).sum := by decide
  have hdescent : baseEnd_3688834 < baseStart_3688834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688862 : List Nat := [4, 3, 1, 2, 1, 2, 1, 8]
def baseStart_3688862 : Nat := 118140960795 + 3688862 * 2 ^ 59
def prefixEnd_3688862 : Nat := 4983230072969 + 3 ^ 40 * 3688862 * 2
def baseEnd_3688862 : Nat := 140308094378211225493351

theorem tailTrace_3688862 : CollatzResearch.WordTrace tailWord_3688862 prefixEnd_3688862 140308094378211225493351 := by
  unfold tailWord_3688862
  simp only [CollatzResearch.WordTrace]
  refine ⟨16817981295236307039656605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89695900241260304211501893 16817981295236307039656605)
  ·
    refine ⟨6306742985713615139871227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16817981295236307039656605 6306742985713615139871227)
    ·
      refine ⟨9460114478570422709806841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6306742985713615139871227 9460114478570422709806841)
      ·
        refine ⟨7095085858927817032355131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9460114478570422709806841 7095085858927817032355131)
        ·
          refine ⟨10642628788391725548532697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7095085858927817032355131 10642628788391725548532697)
          ·
            refine ⟨7981971591293794161399523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10642628788391725548532697 7981971591293794161399523)
            ·
              refine ⟨11972957386940691242099285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7981971591293794161399523 11972957386940691242099285)
              ·
                refine ⟨140308094378211225493351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11972957386940691242099285 140308094378211225493351)
                ·
                  rfl

theorem cell22_3688862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_3688862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688862 prefixEnd_3688862 := by exact prefixLift 3688862
  have htrace : WordTrace (prefixWord ++ tailWord_3688862) baseStart_3688862 baseEnd_3688862 := by
    simpa [prefixWord, tailWord_3688862, baseEnd_3688862] using wordTrace_append hprefix tailTrace_3688862
  have hstable : (prefixWord ++ tailWord_3688862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688862).length < 2 ^ (prefixWord ++ tailWord_3688862).sum := by decide
  have hdescent : baseEnd_3688862 < baseStart_3688862 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688894 : List Nat := [4, 2, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_3688894 : Nat := 118140960795 + 3688894 * 2 ^ 59
def prefixEnd_3688894 : Nat := 4983230072969 + 3 ^ 40 * 3688894 * 2
def baseEnd_3688894 : Nat := 1262783803657863612640061

theorem tailTrace_3688894 : CollatzResearch.WordTrace tailWord_3688894 prefixEnd_3688894 1262783803657863612640061 := by
  unfold tailWord_3688894
  simp only [CollatzResearch.WordTrace]
  refine ⟨16818127187221815722802217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89696678331849683854945157 16818127187221815722802217)
  ·
    refine ⟨12613595390416361792101663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16818127187221815722802217 12613595390416361792101663)
    ·
      refine ⟨18920393085624542688152495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12613595390416361792101663 18920393085624542688152495)
      ·
        refine ⟨28380589628436814032228743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18920393085624542688152495 28380589628436814032228743)
        ·
          refine ⟨42570884442655221048343115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28380589628436814032228743 42570884442655221048343115)
          ·
            refine ⟨63856326663982831572514673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42570884442655221048343115 63856326663982831572514673)
            ·
              refine ⟨47892244997987123679386005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63856326663982831572514673 47892244997987123679386005)
              ·
                refine ⟨2244948984280646422471219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47892244997987123679386005 2244948984280646422471219)
                ·
                  refine ⟨3367423476420969633706829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2244948984280646422471219 3367423476420969633706829)
                  ·
                    refine ⟨1262783803657863612640061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3367423476420969633706829 1262783803657863612640061)
                    ·
                      rfl

theorem cell22_3688894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_3688894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688894 prefixEnd_3688894 := by exact prefixLift 3688894
  have htrace : WordTrace (prefixWord ++ tailWord_3688894) baseStart_3688894 baseEnd_3688894 := by
    simpa [prefixWord, tailWord_3688894, baseEnd_3688894] using wordTrace_append hprefix tailTrace_3688894
  have hstable : (prefixWord ++ tailWord_3688894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688894).length < 2 ^ (prefixWord ++ tailWord_3688894).sum := by decide
  have hdescent : baseEnd_3688894 < baseStart_3688894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688952 : List Nat := [2, 1, 2, 1, 1, 4, 3, 4, 4]
def baseStart_3688952 : Nat := 118140960795 + 3688952 * 2 ^ 59
def prefixEnd_3688952 : Nat := 4983230072969 + 3 ^ 40 * 3688952 * 2
def baseEnd_3688952 : Nat := 420934552747723598229961

theorem tailTrace_3688952 : CollatzResearch.WordTrace tailWord_3688952 prefixEnd_3688952 420934552747723598229961 := by
  unfold tailWord_3688952
  simp only [CollatzResearch.WordTrace]
  refine ⟨67273566465782200844014555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89698088621042934458686073 67273566465782200844014555)
  ·
    refine ⟨100910349698673301266021833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67273566465782200844014555 100910349698673301266021833)
    ·
      refine ⟨75682762274004975949516375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100910349698673301266021833 75682762274004975949516375)
      ·
        refine ⟨113524143411007463924274563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75682762274004975949516375 113524143411007463924274563)
        ·
          refine ⟨170286215116511195886411845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113524143411007463924274563 170286215116511195886411845)
          ·
            refine ⟨31928665334345849228702221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170286215116511195886411845 31928665334345849228702221)
            ·
              refine ⟨11973249500379693460763333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31928665334345849228702221 11973249500379693460763333)
              ·
                refine ⟨2244984281321192523893125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11973249500379693460763333 2244984281321192523893125)
                ·
                  refine ⟨420934552747723598229961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2244984281321192523893125 420934552747723598229961)
                  ·
                    rfl

theorem cell22_3688952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 4, 4].length) (baseStart_3688952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688952 prefixEnd_3688952 := by exact prefixLift 3688952
  have htrace : WordTrace (prefixWord ++ tailWord_3688952) baseStart_3688952 baseEnd_3688952 := by
    simpa [prefixWord, tailWord_3688952, baseEnd_3688952] using wordTrace_append hprefix tailTrace_3688952
  have hstable : (prefixWord ++ tailWord_3688952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688952).length < 2 ^ (prefixWord ++ tailWord_3688952).sum := by decide
  have hdescent : baseEnd_3688952 < baseStart_3688952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3688965 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 4, 4]
def baseStart_3688965 : Nat := 118140960795 + 3688965 * 2 ^ 59
def prefixEnd_3688965 : Nat := 4983230072969 + 3 ^ 40 * 3688965 * 2
def baseEnd_3688965 : Nat := 1262808108408843094114843

theorem tailTrace_3688965 : CollatzResearch.WordTrace tailWord_3688965 prefixEnd_3688965 1262808108408843094114843 := by
  unfold tailWord_3688965
  simp only [CollatzResearch.WordTrace]
  refine ⟨134547607080517304908252349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89698404720344869938834899 134547607080517304908252349)
  ·
    refine ⟨50455352655193989340594631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134547607080517304908252349 50455352655193989340594631)
    ·
      refine ⟨75683028982790984010891947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50455352655193989340594631 75683028982790984010891947)
      ·
        refine ⟨113524543474186476016337921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75683028982790984010891947 113524543474186476016337921)
        ·
          refine ⟨85143407605639857012253441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113524543474186476016337921 85143407605639857012253441)
          ·
            refine ⟨63857555704229892759190081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85143407605639857012253441 63857555704229892759190081)
            ·
              refine ⟨47893166778172419569392561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63857555704229892759190081 47893166778172419569392561)
              ·
                refine ⟨35919875083629314677044421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47893166778172419569392561 35919875083629314677044421)
                ·
                  refine ⟨6734976578180496501945829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35919875083629314677044421 6734976578180496501945829)
                  ·
                    refine ⟨1262808108408843094114843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6734976578180496501945829 1262808108408843094114843)
                    ·
                      rfl

theorem cell22_3688965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_3688965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3688965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3688965 prefixEnd_3688965 := by exact prefixLift 3688965
  have htrace : WordTrace (prefixWord ++ tailWord_3688965) baseStart_3688965 baseEnd_3688965 := by
    simpa [prefixWord, tailWord_3688965, baseEnd_3688965] using wordTrace_append hprefix tailTrace_3688965
  have hstable : (prefixWord ++ tailWord_3688965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3688965).length < 2 ^ (prefixWord ++ tailWord_3688965).sum := by decide
  have hdescent : baseEnd_3688965 < baseStart_3688965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3688965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689010 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_3689010 : Nat := 118140960795 + 3689010 * 2 ^ 59
def prefixEnd_3689010 : Nat := 4983230072969 + 3 ^ 40 * 3689010 * 2
def baseEnd_3689010 : Nat := 1262823512828477976739705

theorem tailTrace_3689010 : CollatzResearch.WordTrace tailWord_3689010 prefixEnd_3689010 1262823512828477976739705 := by
  unfold tailWord_3689010
  simp only [CollatzResearch.WordTrace]
  refine ⟨33637312091338569398410121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89699498910236185062426989 33637312091338569398410121)
  ·
    refine ⟨25227984068503927048807591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33637312091338569398410121 25227984068503927048807591)
    ·
      refine ⟨37841976102755890573211387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25227984068503927048807591 37841976102755890573211387)
      ·
        refine ⟨56762964154133835859817081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37841976102755890573211387 56762964154133835859817081)
        ·
          refine ⟨42572223115600376894862811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56762964154133835859817081 42572223115600376894862811)
          ·
            refine ⟨63858334673400565342294217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42572223115600376894862811 63858334673400565342294217)
            ·
              refine ⟨47893751005050424006720663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63858334673400565342294217 47893751005050424006720663)
              ·
                refine ⟨71840626507575636010080995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47893751005050424006720663 71840626507575636010080995)
                ·
                  refine ⟨107760939761363454015121493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71840626507575636010080995 107760939761363454015121493)
                  ·
                    refine ⟨1262823512828477976739705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107760939761363454015121493 1262823512828477976739705)
                    ·
                      rfl

theorem cell22_3689010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_3689010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689010 prefixEnd_3689010 := by exact prefixLift 3689010
  have htrace : WordTrace (prefixWord ++ tailWord_3689010) baseStart_3689010 baseEnd_3689010 := by
    simpa [prefixWord, tailWord_3689010, baseEnd_3689010] using wordTrace_append hprefix tailTrace_3689010
  have hstable : (prefixWord ++ tailWord_3689010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689010).length < 2 ^ (prefixWord ++ tailWord_3689010).sum := by decide
  have hdescent : baseEnd_3689010 < baseStart_3689010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689040 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 4, 5]
def baseStart_3689040 : Nat := 118140960795 + 3689040 * 2 ^ 59
def prefixEnd_3689040 : Nat := 4983230072969 + 3 ^ 40 * 3689040 * 2
def baseEnd_3689040 : Nat := 1262833782441567898489613

theorem tailTrace_3689040 : CollatzResearch.WordTrace tailWord_3689040 prefixEnd_3689040 1262833782441567898489613 := by
  unfold tailWord_3689040
  simp only [CollatzResearch.WordTrace]
  refine ⟨67275171277622796358616287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89700228370163728478155049 67275171277622796358616287)
  ·
    refine ⟨100912756916434194537924431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67275171277622796358616287 100912756916434194537924431)
    ·
      refine ⟨151369135374651291806886647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100912756916434194537924431 151369135374651291806886647)
      ·
        refine ⟨227053703061976937710329971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151369135374651291806886647 227053703061976937710329971)
        ·
          refine ⟨340580554592965406565494957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227053703061976937710329971 340580554592965406565494957)
          ·
            refine ⟨127717707972362027462060609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 340580554592965406565494957 127717707972362027462060609)
            ·
              refine ⟨95788280979271520596545457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127717707972362027462060609 95788280979271520596545457)
              ·
                refine ⟨71841210734453640447409093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95788280979271520596545457 71841210734453640447409093)
                ·
                  refine ⟨13470227012710057583889205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71841210734453640447409093 13470227012710057583889205)
                  ·
                    refine ⟨1262833782441567898489613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13470227012710057583889205 1262833782441567898489613)
                    ·
                      rfl

theorem cell22_3689040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 4, 5].length) (baseStart_3689040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689040 prefixEnd_3689040 := by exact prefixLift 3689040
  have htrace : WordTrace (prefixWord ++ tailWord_3689040) baseStart_3689040 baseEnd_3689040 := by
    simpa [prefixWord, tailWord_3689040, baseEnd_3689040] using wordTrace_append hprefix tailTrace_3689040
  have hstable : (prefixWord ++ tailWord_3689040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689040).length < 2 ^ (prefixWord ++ tailWord_3689040).sum := by decide
  have hdescent : baseEnd_3689040 < baseStart_3689040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689121 : List Nat := [1, 2, 3, 3, 3, 1, 1, 4, 4]
def baseStart_3689121 : Nat := 118140960795 + 3689121 * 2 ^ 59
def prefixEnd_3689121 : Nat := 4983230072969 + 3 ^ 40 * 3689121 * 2
def baseEnd_3689121 : Nat := 420953836798970229071455

theorem tailTrace_3689121 : CollatzResearch.WordTrace tailWord_3689121 prefixEnd_3689121 420953836798970229071455 := by
  unfold tailWord_3689121
  simp only [CollatzResearch.WordTrace]
  refine ⟨134553296867952143550931217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89702197911968095700620811 134553296867952143550931217)
  ·
    refine ⟨100914972650964107663198413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134553296867952143550931217 100914972650964107663198413)
    ·
      refine ⟨37843114744111540373699405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100914972650964107663198413 37843114744111540373699405)
      ·
        refine ⟨14191168029041827640137277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37843114744111540373699405 14191168029041827640137277)
        ·
          refine ⟨5321688010890685365051479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14191168029041827640137277 5321688010890685365051479)
          ·
            refine ⟨7982532016336028047577219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5321688010890685365051479 7982532016336028047577219)
            ·
              refine ⟨11973798024504042071365829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7982532016336028047577219 11973798024504042071365829)
              ·
                refine ⟨2245087129594507888381093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11973798024504042071365829 2245087129594507888381093)
                ·
                  refine ⟨420953836798970229071455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2245087129594507888381093 420953836798970229071455)
                  ·
                    rfl

theorem cell22_3689121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 4, 4].length) (baseStart_3689121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689121 prefixEnd_3689121 := by exact prefixLift 3689121
  have htrace : WordTrace (prefixWord ++ tailWord_3689121) baseStart_3689121 baseEnd_3689121 := by
    simpa [prefixWord, tailWord_3689121, baseEnd_3689121] using wordTrace_append hprefix tailTrace_3689121
  have hstable : (prefixWord ++ tailWord_3689121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689121).length < 2 ^ (prefixWord ++ tailWord_3689121).sum := by decide
  have hdescent : baseEnd_3689121 < baseStart_3689121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689149 : List Nat := [1, 4, 1, 2, 1, 4, 3, 6]
def baseStart_3689149 : Nat := 118140960795 + 3689149 * 2 ^ 59
def prefixEnd_3689149 : Nat := 4983230072969 + 3 ^ 40 * 3689149 * 2
def baseEnd_3689149 : Nat := 140319010596569771946031

theorem tailTrace_3689149 : CollatzResearch.WordTrace tailWord_3689149 prefixEnd_3689149 140319010596569771946031 := by
  unfold tailWord_3689149
  simp only [CollatzResearch.WordTrace]
  refine ⟨134554318111850704332950501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89702878741233802888633667 134554318111850704332950501)
  ·
    refine ⟨25228934645972007062428219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134554318111850704332950501 25228934645972007062428219)
    ·
      refine ⟨37843401968958010593642329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25228934645972007062428219 37843401968958010593642329)
      ·
        refine ⟨28382551476718507945231747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37843401968958010593642329 28382551476718507945231747)
        ·
          refine ⟨42573827215077761917847621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28382551476718507945231747 42573827215077761917847621)
          ·
            refine ⟨7982592602827080359596429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42573827215077761917847621 7982592602827080359596429)
            ·
              refine ⟨2993472226060155134848661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7982592602827080359596429 2993472226060155134848661)
              ·
                refine ⟨140319010596569771946031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2993472226060155134848661 140319010596569771946031)
                ·
                  rfl

theorem cell22_3689149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 6].length) (baseStart_3689149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689149 prefixEnd_3689149 := by exact prefixLift 3689149
  have htrace : WordTrace (prefixWord ++ tailWord_3689149) baseStart_3689149 baseEnd_3689149 := by
    simpa [prefixWord, tailWord_3689149, baseEnd_3689149] using wordTrace_append hprefix tailTrace_3689149
  have hstable : (prefixWord ++ tailWord_3689149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689149).length < 2 ^ (prefixWord ++ tailWord_3689149).sum := by decide
  have hdescent : baseEnd_3689149 < baseStart_3689149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689170 : List Nat := [3, 2, 2, 2, 4, 1, 1, 2, 2, 3]
def baseStart_3689170 : Nat := 118140960795 + 3689170 * 2 ^ 59
def prefixEnd_3689170 : Nat := 4983230072969 + 3 ^ 40 * 3689170 * 2
def baseEnd_3689170 : Nat := 1262878284098290892739215

theorem tailTrace_3689170 : CollatzResearch.WordTrace tailWord_3689170 prefixEnd_3689170 1262878284098290892739215 := by
  unfold tailWord_3689170
  simp only [CollatzResearch.WordTrace]
  refine ⟨33638771011193656229866241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89703389363183083279643309 33638771011193656229866241)
  ·
    refine ⟨25229078258395242172399681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33638771011193656229866241 25229078258395242172399681)
    ·
      refine ⟨18921808693796431629299761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25229078258395242172399681 18921808693796431629299761)
      ·
        refine ⟨14191356520347323721974821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18921808693796431629299761 14191356520347323721974821)
        ·
          refine ⟨2660879347565123197870279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14191356520347323721974821 2660879347565123197870279)
          ·
            refine ⟨3991319021347684796805419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660879347565123197870279 3991319021347684796805419)
            ·
              refine ⟨5986978532021527195208129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3991319021347684796805419 5986978532021527195208129)
              ·
                refine ⟨4490233899016145396406097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5986978532021527195208129 4490233899016145396406097)
                ·
                  refine ⟨3367675424262109047304573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4490233899016145396406097 3367675424262109047304573)
                  ·
                    refine ⟨1262878284098290892739215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3367675424262109047304573 1262878284098290892739215)
                    ·
                      rfl

theorem cell22_3689170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_3689170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689170 prefixEnd_3689170 := by exact prefixLift 3689170
  have htrace : WordTrace (prefixWord ++ tailWord_3689170) baseStart_3689170 baseEnd_3689170 := by
    simpa [prefixWord, tailWord_3689170, baseEnd_3689170] using wordTrace_append hprefix tailTrace_3689170
  have hstable : (prefixWord ++ tailWord_3689170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689170).length < 2 ^ (prefixWord ++ tailWord_3689170).sum := by decide
  have hdescent : baseEnd_3689170 < baseStart_3689170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689177 : List Nat := [1, 2, 1, 2, 3, 2, 3, 1, 7]
def baseStart_3689177 : Nat := 118140960795 + 3689177 * 2 ^ 59
def prefixEnd_3689177 : Nat := 4983230072969 + 3 ^ 40 * 3689177 * 2
def baseEnd_3689177 : Nat := 420960226780448402604731

theorem tailTrace_3689177 : CollatzResearch.WordTrace tailWord_3689177 prefixEnd_3689177 420960226780448402604731 := by
  unfold tailWord_3689177
  simp only [CollatzResearch.WordTrace]
  refine ⟨134555339355749265114969785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89703559570499510076646523 134555339355749265114969785)
  ·
    refine ⟨100916504516811948836227339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134555339355749265114969785 100916504516811948836227339)
    ·
      refine ⟨151374756775217923254341009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100916504516811948836227339 151374756775217923254341009)
      ·
        refine ⟨113531067581413442440755757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151374756775217923254341009 113531067581413442440755757)
        ·
          refine ⟨42574150343030040915283409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113531067581413442440755757 42574150343030040915283409)
          ·
            refine ⟨31930612757272530686462557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42574150343030040915283409 31930612757272530686462557)
            ·
              refine ⟨11973979783977199007423459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31930612757272530686462557 11973979783977199007423459)
              ·
                refine ⟨17960969675965798511135189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11973979783977199007423459 17960969675965798511135189)
                ·
                  refine ⟨420960226780448402604731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17960969675965798511135189 420960226780448402604731)
                  ·
                    rfl

theorem cell22_3689177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 1, 7].length) (baseStart_3689177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689177 prefixEnd_3689177 := by exact prefixLift 3689177
  have htrace : WordTrace (prefixWord ++ tailWord_3689177) baseStart_3689177 baseEnd_3689177 := by
    simpa [prefixWord, tailWord_3689177, baseEnd_3689177] using wordTrace_append hprefix tailTrace_3689177
  have hstable : (prefixWord ++ tailWord_3689177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689177).length < 2 ^ (prefixWord ++ tailWord_3689177).sum := by decide
  have hdescent : baseEnd_3689177 < baseStart_3689177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689245 : List Nat := [1, 4, 2, 4, 1, 2, 2, 1, 5]
def baseStart_3689245 : Nat := 118140960795 + 3689245 * 2 ^ 59
def prefixEnd_3689245 : Nat := 4983230072969 + 3 ^ 40 * 3689245 * 2
def baseEnd_3689245 : Nat := 420967986043671899037995

theorem tailTrace_3689245 : CollatzResearch.WordTrace tailWord_3689245 prefixEnd_3689245 420967986043671899037995 := by
  unfold tailWord_3689245
  simp only [CollatzResearch.WordTrace]
  refine ⟨134557819519502912728445189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89705213013001941818963459 134557819519502912728445189)
  ·
    refine ⟨25229591159906796136583473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134557819519502912728445189 25229591159906796136583473)
    ·
      refine ⟨18922193369930097102437605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25229591159906796136583473 18922193369930097102437605)
      ·
        refine ⟨3547911256861893206707051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18922193369930097102437605 3547911256861893206707051)
        ·
          refine ⟨5321866885292839810060577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3547911256861893206707051 5321866885292839810060577)
          ·
            refine ⟨3991400163969629857545433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5321866885292839810060577 3991400163969629857545433)
            ·
              refine ⟨2993550122977222393159075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3991400163969629857545433 2993550122977222393159075)
              ·
                refine ⟨4490325184465833589738613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2993550122977222393159075 4490325184465833589738613)
                ·
                  refine ⟨420967986043671899037995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4490325184465833589738613 420967986043671899037995)
                  ·
                    rfl

theorem cell22_3689245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_3689245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689245 prefixEnd_3689245 := by exact prefixLift 3689245
  have htrace : WordTrace (prefixWord ++ tailWord_3689245) baseStart_3689245 baseEnd_3689245 := by
    simpa [prefixWord, tailWord_3689245, baseEnd_3689245] using wordTrace_append hprefix tailTrace_3689245
  have hstable : (prefixWord ++ tailWord_3689245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689245).length < 2 ^ (prefixWord ++ tailWord_3689245).sum := by decide
  have hdescent : baseEnd_3689245 < baseStart_3689245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689258 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 3, 4]
def baseStart_3689258 : Nat := 118140960795 + 3689258 * 2 ^ 59
def prefixEnd_3689258 : Nat := 4983230072969 + 3 ^ 40 * 3689258 * 2
def baseEnd_3689258 : Nat := 1262908408296687996538945

theorem tailTrace_3689258 : CollatzResearch.WordTrace tailWord_3689258 prefixEnd_3689258 1262908408296687996538945 := by
  unfold tailWord_3689258
  simp only [CollatzResearch.WordTrace]
  refine ⟨33639573417113953987167107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89705529112303877299112285 33639573417113953987167107)
  ·
    refine ⟨50459360125670930980750661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33639573417113953987167107 50459360125670930980750661)
    ·
      refine ⟨9461130023563299558890749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50459360125670930980750661 9461130023563299558890749)
      ·
        refine ⟨3547923758836237334584031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9461130023563299558890749 3547923758836237334584031)
        ·
          refine ⟨5321885638254356001876047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3547923758836237334584031 5321885638254356001876047)
          ·
            refine ⟨7982828457381534002814071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5321885638254356001876047 7982828457381534002814071)
            ·
              refine ⟨11974242686072301004221107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7982828457381534002814071 11974242686072301004221107)
              ·
                refine ⟨17961364029108451506331661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11974242686072301004221107 17961364029108451506331661)
                ·
                  refine ⟨6735511510915669314874373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17961364029108451506331661 6735511510915669314874373)
                  ·
                    refine ⟨1262908408296687996538945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6735511510915669314874373 1262908408296687996538945)
                    ·
                      rfl

theorem cell22_3689258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_3689258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689258 prefixEnd_3689258 := by exact prefixLift 3689258
  have htrace : WordTrace (prefixWord ++ tailWord_3689258) baseStart_3689258 baseEnd_3689258 := by
    simpa [prefixWord, tailWord_3689258, baseEnd_3689258] using wordTrace_append hprefix tailTrace_3689258
  have hstable : (prefixWord ++ tailWord_3689258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689258).length < 2 ^ (prefixWord ++ tailWord_3689258).sum := by decide
  have hdescent : baseEnd_3689258 < baseStart_3689258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689299 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 7, 3]
def baseStart_3689299 : Nat := 118140960795 + 3689299 * 2 ^ 59
def prefixEnd_3689299 : Nat := 4983230072969 + 3 ^ 40 * 3689299 * 2
def baseEnd_3689299 : Nat := 1262922443434577556263819

theorem tailTrace_3689299 : CollatzResearch.WordTrace tailWord_3689299 prefixEnd_3689299 1262922443434577556263819 := by
  unfold tailWord_3689299
  simp only [CollatzResearch.WordTrace]
  refine ⟨134559789061307279950910951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89706526040871519967273967 134559789061307279950910951)
  ·
    refine ⟨201839683591960919926366427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134559789061307279950910951 201839683591960919926366427)
    ·
      refine ⟨302759525387941379889549641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201839683591960919926366427 302759525387941379889549641)
      ·
        refine ⟨227069644040956034917162231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 302759525387941379889549641 227069644040956034917162231)
        ·
          refine ⟨340604466061434052375743347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227069644040956034917162231 340604466061434052375743347)
          ·
            refine ⟨510906699092151078563615021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340604466061434052375743347 510906699092151078563615021)
            ·
              refine ⟨191590012159556654461355633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 510906699092151078563615021 191590012159556654461355633)
              ·
                refine ⟨143692509119667490846016725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191590012159556654461355633 143692509119667490846016725)
                ·
                  refine ⟨3367793182492206816703517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 143692509119667490846016725 3367793182492206816703517)
                  ·
                    refine ⟨1262922443434577556263819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3367793182492206816703517 1262922443434577556263819)
                    ·
                      rfl

theorem cell22_3689299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 3].length) (baseStart_3689299 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689299 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689299 prefixEnd_3689299 := by exact prefixLift 3689299
  have htrace : WordTrace (prefixWord ++ tailWord_3689299) baseStart_3689299 baseEnd_3689299 := by
    simpa [prefixWord, tailWord_3689299, baseEnd_3689299] using wordTrace_append hprefix tailTrace_3689299
  have hstable : (prefixWord ++ tailWord_3689299).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689299).length < 2 ^ (prefixWord ++ tailWord_3689299).sum := by decide
  have hdescent : baseEnd_3689299 < baseStart_3689299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689316 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 5, 3]
def baseStart_3689316 : Nat := 118140960795 + 3689316 * 2 ^ 59
def prefixEnd_3689316 : Nat := 4983230072969 + 3 ^ 40 * 3689316 * 2
def baseEnd_3689316 : Nat := 1262928262881995178588767

theorem tailTrace_3689316 : CollatzResearch.WordTrace tailWord_3689316 prefixEnd_3689316 1262928262881995178588767 := by
  unfold tailWord_3689316
  simp only [CollatzResearch.WordTrace]
  refine ⟨67280204551122845927139901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89706939401497127902853201 67280204551122845927139901)
  ·
    refine ⟨25230076706671067222677463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67280204551122845927139901 25230076706671067222677463)
    ·
      refine ⟨37845115060006600834016195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25230076706671067222677463 37845115060006600834016195)
      ·
        refine ⟨56767672590009901251024293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37845115060006600834016195 56767672590009901251024293)
        ·
          refine ⟨10643938610626856484567055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56767672590009901251024293 10643938610626856484567055)
          ·
            refine ⟨15965907915940284726850583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10643938610626856484567055 15965907915940284726850583)
            ·
              refine ⟨23948861873910427090275875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15965907915940284726850583 23948861873910427090275875)
              ·
                refine ⟨35923292810865640635413813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23948861873910427090275875 35923292810865640635413813)
                ·
                  refine ⟨3367808701018653809570045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35923292810865640635413813 3367808701018653809570045)
                  ·
                    refine ⟨1262928262881995178588767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3367808701018653809570045 1262928262881995178588767)
                    ·
                      rfl

theorem cell22_3689316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_3689316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689316 prefixEnd_3689316 := by exact prefixLift 3689316
  have htrace : WordTrace (prefixWord ++ tailWord_3689316) baseStart_3689316 baseEnd_3689316 := by
    simpa [prefixWord, tailWord_3689316, baseEnd_3689316] using wordTrace_append hprefix tailTrace_3689316
  have hstable : (prefixWord ++ tailWord_3689316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689316).length < 2 ^ (prefixWord ++ tailWord_3689316).sum := by decide
  have hdescent : baseEnd_3689316 < baseStart_3689316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689376 : List Nat := [2, 1, 1, 4, 1, 1, 3, 4, 1, 4]
def baseStart_3689376 : Nat := 118140960795 + 3689376 * 2 ^ 59
def prefixEnd_3689376 : Nat := 4983230072969 + 3 ^ 40 * 3689376 * 2
def baseEnd_3689376 : Nat := 1262948802108175022088583

theorem tailTrace_3689376 : CollatzResearch.WordTrace tailWord_3689376 prefixEnd_3689376 1262948802108175022088583 := by
  unfold tailWord_3689376
  simp only [CollatzResearch.WordTrace]
  refine ⟨67281298741014161050731991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89708398321352214734309321 67281298741014161050731991)
  ·
    refine ⟨100921948111521241576097987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67281298741014161050731991 100921948111521241576097987)
    ·
      refine ⟨151382922167281862364146981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100921948111521241576097987 151382922167281862364146981)
      ·
        refine ⟨28384297906365349193277559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151382922167281862364146981 28384297906365349193277559)
        ·
          refine ⟨42576446859548023789916339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28384297906365349193277559 42576446859548023789916339)
          ·
            refine ⟨63864670289322035684874509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42576446859548023789916339 63864670289322035684874509)
            ·
              refine ⟨23949251358495763381827941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63864670289322035684874509 23949251358495763381827941)
              ·
                refine ⟨4490484629717955634092739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23949251358495763381827941 4490484629717955634092739)
                ·
                  refine ⟨6735726944576933451139109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4490484629717955634092739 6735726944576933451139109)
                  ·
                    refine ⟨1262948802108175022088583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6735726944576933451139109 1262948802108175022088583)
                    ·
                      rfl

theorem cell22_3689376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 1, 4].length) (baseStart_3689376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689376 prefixEnd_3689376 := by exact prefixLift 3689376
  have htrace : WordTrace (prefixWord ++ tailWord_3689376) baseStart_3689376 baseEnd_3689376 := by
    simpa [prefixWord, tailWord_3689376, baseEnd_3689376] using wordTrace_append hprefix tailTrace_3689376
  have hstable : (prefixWord ++ tailWord_3689376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689376).length < 2 ^ (prefixWord ++ tailWord_3689376).sum := by decide
  have hdescent : baseEnd_3689376 < baseStart_3689376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689391 : List Nat := [1, 1, 2, 1, 2, 2, 2, 7, 4]
def baseStart_3689391 : Nat := 118140960795 + 3689391 * 2 ^ 59
def prefixEnd_3689391 : Nat := 4983230072969 + 3 ^ 40 * 3689391 * 2
def baseEnd_3689391 : Nat := 420984645638239994321179

theorem tailTrace_3689391 : CollatzResearch.WordTrace tailWord_3689391 prefixEnd_3689391 420984645638239994321179 := by
  unfold tailWord_3689391
  simp only [CollatzResearch.WordTrace]
  refine ⟨134563144576973979663260027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89708763051315986442173351 134563144576973979663260027)
  ·
    refine ⟨201844716865460969494890041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134563144576973979663260027 201844716865460969494890041)
    ·
      refine ⟨151383537649095727121167531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201844716865460969494890041 151383537649095727121167531)
      ·
        refine ⟨227075306473643590681751297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151383537649095727121167531 227075306473643590681751297)
        ·
          refine ⟨170306479855232693011313473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 227075306473643590681751297 170306479855232693011313473)
          ·
            refine ⟨127729859891424519758485105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170306479855232693011313473 127729859891424519758485105)
            ·
              refine ⟨95797394918568389818863829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127729859891424519758485105 95797394918568389818863829)
              ·
                refine ⟨2245251443403946636379621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95797394918568389818863829 2245251443403946636379621)
                ·
                  refine ⟨420984645638239994321179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2245251443403946636379621 420984645638239994321179)
                  ·
                    rfl

theorem cell22_3689391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 7, 4].length) (baseStart_3689391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689391 prefixEnd_3689391 := by exact prefixLift 3689391
  have htrace : WordTrace (prefixWord ++ tailWord_3689391) baseStart_3689391 baseEnd_3689391 := by
    simpa [prefixWord, tailWord_3689391, baseEnd_3689391] using wordTrace_append hprefix tailTrace_3689391
  have hstable : (prefixWord ++ tailWord_3689391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689391).length < 2 ^ (prefixWord ++ tailWord_3689391).sum := by decide
  have hdescent : baseEnd_3689391 < baseStart_3689391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689414 : List Nat := [6, 1, 3, 1, 1, 1, 1, 3, 5]
def baseStart_3689414 : Nat := 118140960795 + 3689414 * 2 ^ 59
def prefixEnd_3689414 : Nat := 4983230072969 + 3 ^ 40 * 3689414 * 2
def baseEnd_3689414 : Nat := 420987270094918529879489

theorem tailTrace_3689414 : CollatzResearch.WordTrace tailWord_3689414 prefixEnd_3689414 420987270094918529879489 := by
  unfold tailWord_3689414
  simp only [CollatzResearch.WordTrace]
  refine ⟨4205124482996582955979603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89709322303927103060898197 4205124482996582955979603)
  ·
    refine ⟨6307686724494874433969405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4205124482996582955979603 6307686724494874433969405)
    ·
      refine ⟨2365382521685577912738527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6307686724494874433969405 2365382521685577912738527)
      ·
        refine ⟨3548073782528366869107791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2365382521685577912738527 3548073782528366869107791)
        ·
          refine ⟨5322110673792550303661687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3548073782528366869107791 5322110673792550303661687)
          ·
            refine ⟨7983166010688825455492531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5322110673792550303661687 7983166010688825455492531)
            ·
              refine ⟨11974749016033238183238797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7983166010688825455492531 11974749016033238183238797)
              ·
                refine ⟨4490530881012464318714549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11974749016033238183238797 4490530881012464318714549)
                ·
                  refine ⟨420987270094918529879489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4490530881012464318714549 420987270094918529879489)
                  ·
                    rfl

theorem cell22_3689414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_3689414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689414 prefixEnd_3689414 := by exact prefixLift 3689414
  have htrace : WordTrace (prefixWord ++ tailWord_3689414) baseStart_3689414 baseEnd_3689414 := by
    simpa [prefixWord, tailWord_3689414, baseEnd_3689414] using wordTrace_append hprefix tailTrace_3689414
  have hstable : (prefixWord ++ tailWord_3689414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689414).length < 2 ^ (prefixWord ++ tailWord_3689414).sum := by decide
  have hdescent : baseEnd_3689414 < baseStart_3689414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689419 : List Nat := [1, 1, 1, 1, 3, 5, 1, 9]
def baseStart_3689419 : Nat := 118140960795 + 3689419 * 2 ^ 59
def prefixEnd_3689419 : Nat := 4983230072969 + 3 ^ 40 * 3689419 * 2
def baseEnd_3689419 : Nat := 140329280209659693695939

theorem tailTrace_3689419 : CollatzResearch.WordTrace tailWord_3689419 prefixEnd_3689419 140329280209659693695939 := by
  unfold tailWord_3689419
  simp only [CollatzResearch.WordTrace]
  refine ⟨134564165820872540445279311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89709443880581693630186207 134564165820872540445279311)
  ·
    refine ⟨201846248731308810667918967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134564165820872540445279311 201846248731308810667918967)
    ·
      refine ⟨302769373096963216001878451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201846248731308810667918967 302769373096963216001878451)
      ·
        refine ⟨454154059645444824002817677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302769373096963216001878451 454154059645444824002817677)
        ·
          refine ⟨170307772367041809001056629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 454154059645444824002817677 170307772367041809001056629)
          ·
            refine ⟨15966353659410169593849059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170307772367041809001056629 15966353659410169593849059)
            ·
              refine ⟨23949530489115254390773589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15966353659410169593849059 23949530489115254390773589)
              ·
                refine ⟨140329280209659693695939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23949530489115254390773589 140329280209659693695939)
                ·
                  rfl

theorem cell22_3689419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 9].length) (baseStart_3689419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689419 prefixEnd_3689419 := by exact prefixLift 3689419
  have htrace : WordTrace (prefixWord ++ tailWord_3689419) baseStart_3689419 baseEnd_3689419 := by
    simpa [prefixWord, tailWord_3689419, baseEnd_3689419] using wordTrace_append hprefix tailTrace_3689419
  have hstable : (prefixWord ++ tailWord_3689419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689419).length < 2 ^ (prefixWord ++ tailWord_3689419).sum := by decide
  have hdescent : baseEnd_3689419 < baseStart_3689419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689423 : List Nat := [1, 1, 2, 1, 1, 7, 1, 3, 2, 3]
def baseStart_3689423 : Nat := 118140960795 + 3689423 * 2 ^ 59
def prefixEnd_3689423 : Nat := 4983230072969 + 3 ^ 40 * 3689423 * 2
def baseEnd_3689423 : Nat := 1262964891168682566163439

theorem tailTrace_3689423 : CollatzResearch.WordTrace tailWord_3689423 prefixEnd_3689423 1262964891168682566163439 := by
  unfold tailWord_3689423
  simp only [CollatzResearch.WordTrace]
  refine ⟨134564311712858049128424923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89709541141905366085616615 134564311712858049128424923)
  ·
    refine ⟨201846467569287073692637385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134564311712858049128424923 201846467569287073692637385)
    ·
      refine ⟨151384850676965305269478039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201846467569287073692637385 151384850676965305269478039)
      ·
        refine ⟨227077276015447957904217059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151384850676965305269478039 227077276015447957904217059)
        ·
          refine ⟨340615914023171936856325589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227077276015447957904217059 340615914023171936856325589)
          ·
            refine ⟨7983185484918092270070131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 340615914023171936856325589 7983185484918092270070131)
            ·
              refine ⟨11974778227377138405105197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7983185484918092270070131 11974778227377138405105197)
              ·
                refine ⟨4490541835266426901914449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11974778227377138405105197 4490541835266426901914449)
                ·
                  refine ⟨3367906376449820176435837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4490541835266426901914449 3367906376449820176435837)
                  ·
                    refine ⟨1262964891168682566163439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3367906376449820176435837 1262964891168682566163439)
                    ·
                      rfl

theorem cell22_3689423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 3].length) (baseStart_3689423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689423 prefixEnd_3689423 := by exact prefixLift 3689423
  have htrace : WordTrace (prefixWord ++ tailWord_3689423) baseStart_3689423 baseEnd_3689423 := by
    simpa [prefixWord, tailWord_3689423, baseEnd_3689423] using wordTrace_append hprefix tailTrace_3689423
  have hstable : (prefixWord ++ tailWord_3689423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689423).length < 2 ^ (prefixWord ++ tailWord_3689423).sum := by decide
  have hdescent : baseEnd_3689423 < baseStart_3689423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689449 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 6, 6]
def baseStart_3689449 : Nat := 118140960795 + 3689449 * 2 ^ 59
def prefixEnd_3689449 : Nat := 4983230072969 + 3 ^ 40 * 3689449 * 2
def baseEnd_3689449 : Nat := 1262973791500027165013359

theorem tailTrace_3689449 : CollatzResearch.WordTrace tailWord_3689449 prefixEnd_3689449 1262973791500027165013359 := by
  unfold tailWord_3689449
  simp only [CollatzResearch.WordTrace]
  refine ⟨134565260010763855568871401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89710173340509237045914267 134565260010763855568871401)
  ·
    refine ⟨100923945008072891676653551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134565260010763855568871401 100923945008072891676653551)
    ·
      refine ⟨151385917512109337514980327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100923945008072891676653551 151385917512109337514980327)
      ·
        refine ⟨227078876268164006272470491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151385917512109337514980327 227078876268164006272470491)
        ·
          refine ⟨340618314402246009408705737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227078876268164006272470491 340618314402246009408705737)
          ·
            refine ⟨255463735801684507056529303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340618314402246009408705737 255463735801684507056529303)
            ·
              refine ⟨383195603702526760584793955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255463735801684507056529303 383195603702526760584793955)
              ·
                refine ⟨574793405553790140877190933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 383195603702526760584793955 574793405553790140877190933)
                ·
                  refine ⟨26943440885333912853618325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 574793405553790140877190933 26943440885333912853618325)
                  ·
                    refine ⟨1262973791500027165013359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26943440885333912853618325 1262973791500027165013359)
                    ·
                      rfl

theorem cell22_3689449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_3689449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689449 prefixEnd_3689449 := by exact prefixLift 3689449
  have htrace : WordTrace (prefixWord ++ tailWord_3689449) baseStart_3689449 baseEnd_3689449 := by
    simpa [prefixWord, tailWord_3689449, baseEnd_3689449] using wordTrace_append hprefix tailTrace_3689449
  have hstable : (prefixWord ++ tailWord_3689449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689449).length < 2 ^ (prefixWord ++ tailWord_3689449).sum := by decide
  have hdescent : baseEnd_3689449 < baseStart_3689449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689470 : List Nat := [4, 2, 2, 2, 2, 2, 1, 7]
def baseStart_3689470 : Nat := 118140960795 + 3689470 * 2 ^ 59
def prefixEnd_3689470 : Nat := 4983230072969 + 3 ^ 40 * 3689470 * 2
def baseEnd_3689470 : Nat := 140331220025465567804255

theorem tailTrace_3689470 : CollatzResearch.WordTrace tailWord_3689470 prefixEnd_3689470 140331220025465567804255 := by
  unfold tailWord_3689470
  simp only [CollatzResearch.WordTrace]
  refine ⟨16820753242960972019423233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89710683962458517436923909 16820753242960972019423233)
  ·
    refine ⟨12615564932220729014567425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16820753242960972019423233 12615564932220729014567425)
    ·
      refine ⟨9461673699165546760925569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12615564932220729014567425 9461673699165546760925569)
      ·
        refine ⟨7096255274374160070694177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9461673699165546760925569 7096255274374160070694177)
        ·
          refine ⟨5322191455780620053020633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7096255274374160070694177 5322191455780620053020633)
          ·
            refine ⟨3991643591835465039765475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5322191455780620053020633 3991643591835465039765475)
            ·
              refine ⟨5987465387753197559648213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3991643591835465039765475 5987465387753197559648213)
              ·
                refine ⟨140331220025465567804255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5987465387753197559648213 140331220025465567804255)
                ·
                  rfl

theorem cell22_3689470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_3689470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689470 prefixEnd_3689470 := by exact prefixLift 3689470
  have htrace : WordTrace (prefixWord ++ tailWord_3689470) baseStart_3689470 baseEnd_3689470 := by
    simpa [prefixWord, tailWord_3689470, baseEnd_3689470] using wordTrace_append hprefix tailTrace_3689470
  have hstable : (prefixWord ++ tailWord_3689470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689470).length < 2 ^ (prefixWord ++ tailWord_3689470).sum := by decide
  have hdescent : baseEnd_3689470 < baseStart_3689470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689573 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 2, 4]
def baseStart_3689573 : Nat := 118140960795 + 3689573 * 2 ^ 59
def prefixEnd_3689573 : Nat := 4983230072969 + 3 ^ 40 * 3689573 * 2
def baseEnd_3689573 : Nat := 1263016239234132174912979

theorem tailTrace_3689573 : CollatzResearch.WordTrace tailWord_3689573 prefixEnd_3689573 1263016239234132174912979 := by
  unfold tailWord_3689573
  simp only [CollatzResearch.WordTrace]
  refine ⟨134569782662314624746385373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89713188441543083164256915 134569782662314624746385373)
  ·
    refine ⟨50463668498367984279894515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134569782662314624746385373 50463668498367984279894515)
    ·
      refine ⟨75695502747551976419841773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50463668498367984279894515 75695502747551976419841773)
      ·
        refine ⟨28385813530331991157440665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75695502747551976419841773 28385813530331991157440665)
        ·
          refine ⟨21289360147748993368080499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28385813530331991157440665 21289360147748993368080499)
          ·
            refine ⟨31934040221623490052120749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21289360147748993368080499 31934040221623490052120749)
            ·
              refine ⟨11975265083108808769545281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31934040221623490052120749 11975265083108808769545281)
              ·
                refine ⟨8981448812331606577158961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11975265083108808769545281 8981448812331606577158961)
                ·
                  refine ⟨6736086609248704932869221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8981448812331606577158961 6736086609248704932869221)
                  ·
                    refine ⟨1263016239234132174912979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6736086609248704932869221 1263016239234132174912979)
                    ·
                      rfl

theorem cell22_3689573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_3689573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689573 prefixEnd_3689573 := by exact prefixLift 3689573
  have htrace : WordTrace (prefixWord ++ tailWord_3689573) baseStart_3689573 baseEnd_3689573 := by
    simpa [prefixWord, tailWord_3689573, baseEnd_3689573] using wordTrace_append hprefix tailTrace_3689573
  have hstable : (prefixWord ++ tailWord_3689573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689573).length < 2 ^ (prefixWord ++ tailWord_3689573).sum := by decide
  have hdescent : baseEnd_3689573 < baseStart_3689573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689603 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 5, 3]
def baseStart_3689603 : Nat := 118140960795 + 3689603 * 2 ^ 59
def prefixEnd_3689603 : Nat := 4983230072969 + 3 ^ 40 * 3689603 * 2
def baseEnd_3689603 : Nat := 1263026508847222096662887

theorem tailTrace_3689603 : CollatzResearch.WordTrace tailWord_3689603 prefixEnd_3689603 1263026508847222096662887 := by
  unfold tailWord_3689603
  simp only [CollatzResearch.WordTrace]
  refine ⟨134570876852205939869977463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89713917901470626579984975 134570876852205939869977463)
  ·
    refine ⟨201856315278308909804966195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134570876852205939869977463 201856315278308909804966195)
    ·
      refine ⟨302784472917463364707449293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201856315278308909804966195 302784472917463364707449293)
      ·
        refine ⟨113544177344048761765293485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302784472917463364707449293 113544177344048761765293485)
        ·
          refine ⟨42579066504018285661985057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113544177344048761765293485 42579066504018285661985057)
          ·
            refine ⟨31934299878013714246488793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42579066504018285661985057 31934299878013714246488793)
            ·
              refine ⟨23950724908510285684866595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31934299878013714246488793 23950724908510285684866595)
              ·
                refine ⟨35926087362765428527299893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23950724908510285684866595 35926087362765428527299893)
                ·
                  refine ⟨3368070690259258924434365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35926087362765428527299893 3368070690259258924434365)
                  ·
                    refine ⟨1263026508847222096662887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3368070690259258924434365 1263026508847222096662887)
                    ·
                      rfl

theorem cell22_3689603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 3].length) (baseStart_3689603 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689603 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689603 prefixEnd_3689603 := by exact prefixLift 3689603
  have htrace : WordTrace (prefixWord ++ tailWord_3689603) baseStart_3689603 baseEnd_3689603 := by
    simpa [prefixWord, tailWord_3689603, baseEnd_3689603] using wordTrace_append hprefix tailTrace_3689603
  have hstable : (prefixWord ++ tailWord_3689603).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689603).length < 2 ^ (prefixWord ++ tailWord_3689603).sum := by decide
  have hdescent : baseEnd_3689603 < baseStart_3689603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689616 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 7]
def baseStart_3689616 : Nat := 118140960795 + 3689616 * 2 ^ 59
def prefixEnd_3689616 : Nat := 4983230072969 + 3 ^ 40 * 3689616 * 2
def baseEnd_3689616 : Nat := 421010319670964798695949

theorem tailTrace_3689616 : CollatzResearch.WordTrace tailWord_3689616 prefixEnd_3689616 421010319670964798695949 := by
  unfold tailWord_3689616
  simp only [CollatzResearch.WordTrace]
  refine ⟨67285675500579421545100351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89714234000772562060133801 67285675500579421545100351)
  ·
    refine ⟨100928513250869132317650527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67285675500579421545100351 100928513250869132317650527)
    ·
      refine ⟨151392769876303698476475791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100928513250869132317650527 151392769876303698476475791)
      ·
        refine ⟨227089154814455547714713687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151392769876303698476475791 227089154814455547714713687)
        ·
          refine ⟨340633732221683321572070531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227089154814455547714713687 340633732221683321572070531)
          ·
            refine ⟨510950598332524982358105797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 340633732221683321572070531 510950598332524982358105797)
            ·
              refine ⟨95803237187348434192144837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 510950598332524982358105797 95803237187348434192144837)
              ·
                refine ⟨17963106972627831411027157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95803237187348434192144837 17963106972627831411027157)
                ·
                  refine ⟨421010319670964798695949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17963106972627831411027157 421010319670964798695949)
                  ·
                    rfl

theorem cell22_3689616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 7].length) (baseStart_3689616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689616 prefixEnd_3689616 := by exact prefixLift 3689616
  have htrace : WordTrace (prefixWord ++ tailWord_3689616) baseStart_3689616 baseEnd_3689616 := by
    simpa [prefixWord, tailWord_3689616, baseEnd_3689616] using wordTrace_append hprefix tailTrace_3689616
  have hstable : (prefixWord ++ tailWord_3689616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689616).length < 2 ^ (prefixWord ++ tailWord_3689616).sum := by decide
  have hdescent : baseEnd_3689616 < baseStart_3689616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689637 : List Nat := [1, 3, 1, 2, 1, 5, 1, 4, 1, 3]
def baseStart_3689637 : Nat := 118140960795 + 3689637 * 2 ^ 59
def prefixEnd_3689637 : Nat := 4983230072969 + 3 ^ 40 * 3689637 * 2
def baseEnd_3689637 : Nat := 1263038147742057341312783

theorem tailTrace_3689637 : CollatzResearch.WordTrace tailWord_3689637 prefixEnd_3689637 1263038147742057341312783 := by
  unfold tailWord_3689637
  simp only [CollatzResearch.WordTrace]
  refine ⟨134572116934082763676715165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89714744622721842451143443 134572116934082763676715165)
  ·
    refine ⟨50464543850281036378768187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134572116934082763676715165 50464543850281036378768187)
    ·
      refine ⟨75696815775421554568152281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50464543850281036378768187 75696815775421554568152281)
      ·
        refine ⟨56772611831566165926114211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75696815775421554568152281 56772611831566165926114211)
        ·
          refine ⟨85158917747349248889171317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56772611831566165926114211 85158917747349248889171317)
          ·
            refine ⟨7983648538813992083359811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85158917747349248889171317 7983648538813992083359811)
            ·
              refine ⟨11975472808220988125039717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7983648538813992083359811 11975472808220988125039717)
              ·
                refine ⟨2245401151541435273444947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11975472808220988125039717 2245401151541435273444947)
                ·
                  refine ⟨3368101727312152910167421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2245401151541435273444947 3368101727312152910167421)
                  ·
                    refine ⟨1263038147742057341312783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3368101727312152910167421 1263038147742057341312783)
                    ·
                      rfl

theorem cell22_3689637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_3689637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689637 prefixEnd_3689637 := by exact prefixLift 3689637
  have htrace : WordTrace (prefixWord ++ tailWord_3689637) baseStart_3689637 baseEnd_3689637 := by
    simpa [prefixWord, tailWord_3689637, baseEnd_3689637] using wordTrace_append hprefix tailTrace_3689637
  have hstable : (prefixWord ++ tailWord_3689637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689637).length < 2 ^ (prefixWord ++ tailWord_3689637).sum := by decide
  have hdescent : baseEnd_3689637 < baseStart_3689637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689663 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 3, 4]
def baseStart_3689663 : Nat := 118140960795 + 3689663 * 2 ^ 59
def prefixEnd_3689663 : Nat := 4983230072969 + 3 ^ 40 * 3689663 * 2
def baseEnd_3689663 : Nat := 1263047048073401940162703

theorem tailTrace_3689663 : CollatzResearch.WordTrace tailWord_3689663 prefixEnd_3689663 1263047048073401940162703 := by
  unfold tailWord_3689663
  simp only [CollatzResearch.WordTrace]
  refine ⟨134573065231988570117161643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89715376821325713411441095 134573065231988570117161643)
  ·
    refine ⟨201859597847982855175742465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134573065231988570117161643 201859597847982855175742465)
    ·
      refine ⟨151394698385987141381806849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201859597847982855175742465 151394698385987141381806849)
      ·
        refine ⟨113546023789490356036355137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151394698385987141381806849 113546023789490356036355137)
        ·
          refine ⟨85159517842117767027266353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113546023789490356036355137 85159517842117767027266353)
          ·
            refine ⟨63869638381588325270449765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85159517842117767027266353 63869638381588325270449765)
            ·
              refine ⟨11975557196547810988209331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63869638381588325270449765 11975557196547810988209331)
              ·
                refine ⟨17963335794821716482313997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11975557196547810988209331 17963335794821716482313997)
                ·
                  refine ⟨6736250923058143680867749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17963335794821716482313997 6736250923058143680867749)
                  ·
                    refine ⟨1263047048073401940162703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6736250923058143680867749 1263047048073401940162703)
                    ·
                      rfl

theorem cell22_3689663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_3689663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689663 prefixEnd_3689663 := by exact prefixLift 3689663
  have htrace : WordTrace (prefixWord ++ tailWord_3689663) baseStart_3689663 baseEnd_3689663 := by
    simpa [prefixWord, tailWord_3689663, baseEnd_3689663] using wordTrace_append hprefix tailTrace_3689663
  have hstable : (prefixWord ++ tailWord_3689663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689663).length < 2 ^ (prefixWord ++ tailWord_3689663).sum := by decide
  have hdescent : baseEnd_3689663 < baseStart_3689663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689684 : List Nat := [2, 4, 1, 4, 1, 2, 1, 2, 5]
def baseStart_3689684 : Nat := 118140960795 + 3689684 * 2 ^ 59
def prefixEnd_3689684 : Nat := 4983230072969 + 3 ^ 40 * 3689684 * 2
def baseEnd_3689684 : Nat := 421018078934188295129213

theorem tailTrace_3689684 : CollatzResearch.WordTrace tailWord_3689684 prefixEnd_3689684 421018078934188295129213 := by
  unfold tailWord_3689684
  simp only [CollatzResearch.WordTrace]
  refine ⟨67286915582456245351838053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89715887443274993802450737 67286915582456245351838053)
  ·
    refine ⟨12616296671710546003469635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67286915582456245351838053 12616296671710546003469635)
    ·
      refine ⟨18924445007565819005204453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12616296671710546003469635 18924445007565819005204453)
      ·
        refine ⟨3548333438918591063475835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18924445007565819005204453 3548333438918591063475835)
        ·
          refine ⟨5322500158377886595213753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3548333438918591063475835 5322500158377886595213753)
          ·
            refine ⟨3991875118783414946410315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5322500158377886595213753 3991875118783414946410315)
            ·
              refine ⟨5987812678175122419615473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3991875118783414946410315 5987812678175122419615473)
              ·
                refine ⟨4490859508631341814711605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5987812678175122419615473 4490859508631341814711605)
                ·
                  refine ⟨421018078934188295129213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4490859508631341814711605 421018078934188295129213)
                  ·
                    rfl

theorem cell22_3689684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_3689684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689684 prefixEnd_3689684 := by exact prefixLift 3689684
  have htrace : WordTrace (prefixWord ++ tailWord_3689684) baseStart_3689684 baseEnd_3689684 := by
    simpa [prefixWord, tailWord_3689684, baseEnd_3689684] using wordTrace_append hprefix tailTrace_3689684
  have hstable : (prefixWord ++ tailWord_3689684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689684).length < 2 ^ (prefixWord ++ tailWord_3689684).sum := by decide
  have hdescent : baseEnd_3689684 < baseStart_3689684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689695 : List Nat := [1, 1, 2, 3, 2, 1, 4, 4, 4]
def baseStart_3689695 : Nat := 118140960795 + 3689695 * 2 ^ 59
def prefixEnd_3689695 : Nat := 4983230072969 + 3 ^ 40 * 3689695 * 2
def baseEnd_3689695 : Nat := 421019334109121507787535

theorem tailTrace_3689695 : CollatzResearch.WordTrace tailWord_3689695 prefixEnd_3689695 421019334109121507787535 := by
  unfold tailWord_3689695
  simp only [CollatzResearch.WordTrace]
  refine ⟨134574232367872639582326539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89716154911915093054884359 134574232367872639582326539)
  ·
    refine ⟨201861348551808959373489809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134574232367872639582326539 201861348551808959373489809)
    ·
      refine ⟨151396011413856719530117357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201861348551808959373489809 151396011413856719530117357)
      ·
        refine ⟨56773504280196269823794009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151396011413856719530117357 56773504280196269823794009)
        ·
          refine ⟨42580128210147202367845507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56773504280196269823794009 42580128210147202367845507)
          ·
            refine ⟨63870192315220803551768261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42580128210147202367845507 63870192315220803551768261)
            ·
              refine ⟨11975661059103900665956549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63870192315220803551768261 11975661059103900665956549)
              ·
                refine ⟨2245436448581981374866853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11975661059103900665956549 2245436448581981374866853)
                ·
                  refine ⟨421019334109121507787535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2245436448581981374866853 421019334109121507787535)
                  ·
                    rfl

theorem cell22_3689695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 4, 4].length) (baseStart_3689695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689695 prefixEnd_3689695 := by exact prefixLift 3689695
  have htrace : WordTrace (prefixWord ++ tailWord_3689695) baseStart_3689695 baseEnd_3689695 := by
    simpa [prefixWord, tailWord_3689695, baseEnd_3689695] using wordTrace_append hprefix tailTrace_3689695
  have hstable : (prefixWord ++ tailWord_3689695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689695).length < 2 ^ (prefixWord ++ tailWord_3689695).sum := by decide
  have hdescent : baseEnd_3689695 < baseStart_3689695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689708 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 1, 6]
def baseStart_3689708 : Nat := 118140960795 + 3689708 * 2 ^ 59
def prefixEnd_3689708 : Nat := 4983230072969 + 3 ^ 40 * 3689708 * 2
def baseEnd_3689708 : Nat := 1263062452493036822787565

theorem tailTrace_3689708 : CollatzResearch.WordTrace tailWord_3689708 prefixEnd_3689708 1263062452493036822787565 := by
  unfold tailWord_3689708
  simp only [CollatzResearch.WordTrace]
  refine ⟨67287353258412771401274889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89716471011217028535033185 67287353258412771401274889)
  ·
    refine ⟨50465514943809578550956167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67287353258412771401274889 50465514943809578550956167)
    ·
      refine ⟨75698272415714367826434251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50465514943809578550956167 75698272415714367826434251)
      ·
        refine ⟨113547408623571551739651377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75698272415714367826434251 113547408623571551739651377)
        ·
          refine ⟨85160556467678663804738533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113547408623571551739651377 85160556467678663804738533)
          ·
            refine ⟨15967604337689749463388475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85160556467678663804738533 15967604337689749463388475)
            ·
              refine ⟨23951406506534624195082713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15967604337689749463388475 23951406506534624195082713)
              ·
                refine ⟨17963554879900968146312035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23951406506534624195082713 17963554879900968146312035)
                ·
                  refine ⟨26945332319851452219468053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17963554879900968146312035 26945332319851452219468053)
                  ·
                    refine ⟨1263062452493036822787565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26945332319851452219468053 1263062452493036822787565)
                    ·
                      rfl

theorem cell22_3689708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_3689708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689708 prefixEnd_3689708 := by exact prefixLift 3689708
  have htrace : WordTrace (prefixWord ++ tailWord_3689708) baseStart_3689708 baseEnd_3689708 := by
    simpa [prefixWord, tailWord_3689708, baseEnd_3689708] using wordTrace_append hprefix tailTrace_3689708
  have hstable : (prefixWord ++ tailWord_3689708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689708).length < 2 ^ (prefixWord ++ tailWord_3689708).sum := by decide
  have hdescent : baseEnd_3689708 < baseStart_3689708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689710 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_3689710 : Nat := 118140960795 + 3689710 * 2 ^ 59
def prefixEnd_3689710 : Nat := 4983230072969 + 3 ^ 40 * 3689710 * 2
def baseEnd_3689710 : Nat := 1263063137133909484237559

theorem tailTrace_3689710 : CollatzResearch.WordTrace tailWord_3689710 prefixEnd_3689710 1263063137133909484237559 := by
  unfold tailWord_3689710
  simp only [CollatzResearch.WordTrace]
  refine ⟨16821847432852287143015323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89716519641878864762748389 16821847432852287143015323)
  ·
    refine ⟨25232771149278430714522985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16821847432852287143015323 25232771149278430714522985)
    ·
      refine ⟨18924578361958823035892239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25232771149278430714522985 18924578361958823035892239)
      ·
        refine ⟨28386867542938234553838359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18924578361958823035892239 28386867542938234553838359)
        ·
          refine ⟨42580301314407351830757539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28386867542938234553838359 42580301314407351830757539)
          ·
            refine ⟨63870451971611027746136309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42580301314407351830757539 63870451971611027746136309)
            ·
              refine ⟨5987854872338533851200279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63870451971611027746136309 5987854872338533851200279)
              ·
                refine ⟨8981782308507800776800419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5987854872338533851200279 8981782308507800776800419)
                ·
                  refine ⟨13472673462761701165200629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8981782308507800776800419 13472673462761701165200629)
                  ·
                    refine ⟨1263063137133909484237559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13472673462761701165200629 1263063137133909484237559)
                    ·
                      rfl

theorem cell22_3689710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_3689710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689710 prefixEnd_3689710 := by exact prefixLift 3689710
  have htrace : WordTrace (prefixWord ++ tailWord_3689710) baseStart_3689710 baseEnd_3689710 := by
    simpa [prefixWord, tailWord_3689710, baseEnd_3689710] using wordTrace_append hprefix tailTrace_3689710
  have hstable : (prefixWord ++ tailWord_3689710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689710).length < 2 ^ (prefixWord ++ tailWord_3689710).sum := by decide
  have hdescent : baseEnd_3689710 < baseStart_3689710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689746 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 6]
def baseStart_3689746 : Nat := 118140960795 + 3689746 * 2 ^ 59
def prefixEnd_3689746 : Nat := 4983230072969 + 3 ^ 40 * 3689746 * 2
def baseEnd_3689746 : Nat := 421025153556539130112483

theorem tailTrace_3689746 : CollatzResearch.WordTrace tailWord_3689746 prefixEnd_3689746 421025153556539130112483 := by
  unfold tailWord_3689746
  simp only [CollatzResearch.WordTrace]
  refine ⟨33644023122671968823108273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89717394993791916861622061 33644023122671968823108273)
  ·
    refine ⟨25233017342003976617331205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33644023122671968823108273 25233017342003976617331205)
    ·
      refine ⟨4731190751625745615749601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25233017342003976617331205 4731190751625745615749601)
      ·
        refine ⟨3548393063719309211812201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4731190751625745615749601 3548393063719309211812201)
        ·
          refine ⟨2661294797789481908859151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3548393063719309211812201 2661294797789481908859151)
          ·
            refine ⟨3991942196684222863288727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661294797789481908859151 3991942196684222863288727)
            ·
              refine ⟨5987913295026334294933091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3991942196684222863288727 5987913295026334294933091)
              ·
                refine ⟨8981869942539501442399637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5987913295026334294933091 8981869942539501442399637)
                ·
                  refine ⟨421025153556539130112483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8981869942539501442399637 421025153556539130112483)
                  ·
                    rfl

theorem cell22_3689746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_3689746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689746 prefixEnd_3689746 := by exact prefixLift 3689746
  have htrace : WordTrace (prefixWord ++ tailWord_3689746) baseStart_3689746 baseEnd_3689746 := by
    simpa [prefixWord, tailWord_3689746, baseEnd_3689746] using wordTrace_append hprefix tailTrace_3689746
  have hstable : (prefixWord ++ tailWord_3689746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689746).length < 2 ^ (prefixWord ++ tailWord_3689746).sum := by decide
  have hdescent : baseEnd_3689746 < baseStart_3689746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689783 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 6, 5]
def baseStart_3689783 : Nat := 118140960795 + 3689783 * 2 ^ 59
def prefixEnd_3689783 : Nat := 4983230072969 + 3 ^ 40 * 3689783 * 2
def baseEnd_3689783 : Nat := 1263088126525761627162335

theorem tailTrace_3689783 : CollatzResearch.WordTrace tailWord_3689783 prefixEnd_3689783 1263088126525761627162335 := by
  unfold tailWord_3689783
  simp only [CollatzResearch.WordTrace]
  refine ⟨134577441991553830611530003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89718294661035887074353335 134577441991553830611530003)
  ·
    refine ⟨201866162987330745917295005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134577441991553830611530003 201866162987330745917295005)
    ·
      refine ⟨75699811120249029718985627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201866162987330745917295005 75699811120249029718985627)
      ·
        refine ⟨113549716680373544578478441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75699811120249029718985627 113549716680373544578478441)
        ·
          refine ⟨85162287510280158433858831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113549716680373544578478441 85162287510280158433858831)
          ·
            refine ⟨127743431265420237650788247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85162287510280158433858831 127743431265420237650788247)
            ·
              refine ⟨191615146898130356476182371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127743431265420237650788247 191615146898130356476182371)
              ·
                refine ⟨287422720347195534714273557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 191615146898130356476182371 287422720347195534714273557)
                ·
                  refine ⟨13472940016274790689731573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 287422720347195534714273557 13472940016274790689731573)
                  ·
                    refine ⟨1263088126525761627162335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13472940016274790689731573 1263088126525761627162335)
                    ·
                      rfl

theorem cell22_3689783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_3689783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689783 prefixEnd_3689783 := by exact prefixLift 3689783
  have htrace : WordTrace (prefixWord ++ tailWord_3689783) baseStart_3689783 baseEnd_3689783 := by
    simpa [prefixWord, tailWord_3689783, baseEnd_3689783] using wordTrace_append hprefix tailTrace_3689783
  have hstable : (prefixWord ++ tailWord_3689783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689783).length < 2 ^ (prefixWord ++ tailWord_3689783).sum := by decide
  have hdescent : baseEnd_3689783 < baseStart_3689783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689815 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 3, 4]
def baseStart_3689815 : Nat := 118140960795 + 3689815 * 2 ^ 59
def prefixEnd_3689815 : Nat := 4983230072969 + 3 ^ 40 * 3689815 * 2
def baseEnd_3689815 : Nat := 1263099080779724210362237

theorem tailTrace_3689815 : CollatzResearch.WordTrace tailWord_3689815 prefixEnd_3689815 1263099080779724210362237 := by
  unfold tailWord_3689815
  simp only [CollatzResearch.WordTrace]
  refine ⟨134578609127437900076694899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89719072751625266717796599 134578609127437900076694899)
  ·
    refine ⟨201867913691156850115042349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134578609127437900076694899 201867913691156850115042349)
    ·
      refine ⟨75700467634183818793140881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201867913691156850115042349 75700467634183818793140881)
      ·
        refine ⟨56775350725637864094855661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75700467634183818793140881 56775350725637864094855661)
        ·
          refine ⟨21290756522114199035570873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56775350725637864094855661 21290756522114199035570873)
          ·
            refine ⟨15968067391585649276678155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21290756522114199035570873 15968067391585649276678155)
            ·
              refine ⟨23952101087378473915017233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15968067391585649276678155 23952101087378473915017233)
              ·
                refine ⟨17964075815533855436262925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23952101087378473915017233 17964075815533855436262925)
                ·
                  refine ⟨6736528430825195788598597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17964075815533855436262925 6736528430825195788598597)
                  ·
                    refine ⟨1263099080779724210362237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6736528430825195788598597 1263099080779724210362237)
                    ·
                      rfl

theorem cell22_3689815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_3689815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689815 prefixEnd_3689815 := by exact prefixLift 3689815
  have htrace : WordTrace (prefixWord ++ tailWord_3689815) baseStart_3689815 baseEnd_3689815 := by
    simpa [prefixWord, tailWord_3689815, baseEnd_3689815] using wordTrace_append hprefix tailTrace_3689815
  have hstable : (prefixWord ++ tailWord_3689815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689815).length < 2 ^ (prefixWord ++ tailWord_3689815).sum := by decide
  have hdescent : baseEnd_3689815 < baseStart_3689815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689847 : List Nat := [1, 1, 3, 1, 1, 2, 6, 3, 4]
def baseStart_3689847 : Nat := 118140960795 + 3689847 * 2 ^ 59
def prefixEnd_3689847 : Nat := 4983230072969 + 3 ^ 40 * 3689847 * 2
def baseEnd_3689847 : Nat := 421036678344562264520713

theorem tailTrace_3689847 : CollatzResearch.WordTrace tailWord_3689847 prefixEnd_3689847 421036678344562264520713 := by
  unfold tailWord_3689847
  simp only [CollatzResearch.WordTrace]
  refine ⟨134579776263321969541859795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89719850842214646361239863 134579776263321969541859795)
  ·
    refine ⟨201869664394982954312789693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134579776263321969541859795 201869664394982954312789693)
    ·
      refine ⟨75701124148118607867296135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201869664394982954312789693 75701124148118607867296135)
      ·
        refine ⟨113551686222177911800944203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75701124148118607867296135 113551686222177911800944203)
        ·
          refine ⟨170327529333266867701416305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113551686222177911800944203 170327529333266867701416305)
          ·
            refine ⟨127745646999950150776062229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 170327529333266867701416305 127745646999950150776062229)
            ·
              refine ⟨5988077203122663317627917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127745646999950150776062229 5988077203122663317627917)
              ·
                refine ⟨2245528951170998744110469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5988077203122663317627917 2245528951170998744110469)
                ·
                  refine ⟨421036678344562264520713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2245528951170998744110469 421036678344562264520713)
                  ·
                    rfl

theorem cell22_3689847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 3, 4].length) (baseStart_3689847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689847 prefixEnd_3689847 := by exact prefixLift 3689847
  have htrace : WordTrace (prefixWord ++ tailWord_3689847) baseStart_3689847 baseEnd_3689847 := by
    simpa [prefixWord, tailWord_3689847, baseEnd_3689847] using wordTrace_append hprefix tailTrace_3689847
  have hstable : (prefixWord ++ tailWord_3689847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689847).length < 2 ^ (prefixWord ++ tailWord_3689847).sum := by decide
  have hdescent : baseEnd_3689847 < baseStart_3689847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689920 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 7]
def baseStart_3689920 : Nat := 118140960795 + 3689920 * 2 ^ 59
def prefixEnd_3689920 : Nat := 4983230072969 + 3 ^ 40 * 3689920 * 2
def baseEnd_3689920 : Nat := 421045008141846312162305

theorem tailTrace_3689920 : CollatzResearch.WordTrace tailWord_3689920 prefixEnd_3689920 421045008141846312162305 := by
  unfold tailWord_3689920
  simp only [CollatzResearch.WordTrace]
  refine ⟨67291219396028751504633607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89721625861371668672844809 67291219396028751504633607)
  ·
    refine ⟨100936829094043127256950411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67291219396028751504633607 100936829094043127256950411)
    ·
      refine ⟨151405243641064690885425617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100936829094043127256950411 151405243641064690885425617)
      ·
        refine ⟨113553932730798518164069213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151405243641064690885425617 113553932730798518164069213)
        ·
          refine ⟨42582724774049444311525955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113553932730798518164069213 42582724774049444311525955)
          ·
            refine ⟨63874087161074166467288933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42582724774049444311525955 63874087161074166467288933)
            ·
              refine ⟨11976391342701406212616675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63874087161074166467288933 11976391342701406212616675)
              ·
                refine ⟨17964587014052109318925013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11976391342701406212616675 17964587014052109318925013)
                ·
                  refine ⟨421045008141846312162305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17964587014052109318925013 421045008141846312162305)
                  ·
                    rfl

theorem cell22_3689920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 7].length) (baseStart_3689920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689920 prefixEnd_3689920 := by exact prefixLift 3689920
  have htrace : WordTrace (prefixWord ++ tailWord_3689920) baseStart_3689920 baseEnd_3689920 := by
    simpa [prefixWord, tailWord_3689920, baseEnd_3689920] using wordTrace_append hprefix tailTrace_3689920
  have hstable : (prefixWord ++ tailWord_3689920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689920).length < 2 ^ (prefixWord ++ tailWord_3689920).sum := by decide
  have hdescent : baseEnd_3689920 < baseStart_3689920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689935 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 2, 5]
def baseStart_3689935 : Nat := 118140960795 + 3689935 * 2 ^ 59
def prefixEnd_3689935 : Nat := 4983230072969 + 3 ^ 40 * 3689935 * 2
def baseEnd_3689935 : Nat := 1263140159232083897361869

theorem tailTrace_3689935 : CollatzResearch.WordTrace tailWord_3689935 prefixEnd_3689935 1263140159232083897361869 := by
  unfold tailWord_3689935
  simp only [CollatzResearch.WordTrace]
  refine ⟨134582985887003160571063259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89721990591335440380708839 134582985887003160571063259)
  ·
    refine ⟨201874478830504740856594889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134582985887003160571063259 201874478830504740856594889)
    ·
      refine ⟨151405859122878555642446167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201874478830504740856594889 151405859122878555642446167)
      ·
        refine ⟨227108788684317833463669251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151405859122878555642446167 227108788684317833463669251)
        ·
          refine ⟨340663183026476750195503877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227108788684317833463669251 340663183026476750195503877)
          ·
            refine ⟨63874346817464390661656977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 340663183026476750195503877 63874346817464390661656977)
            ·
              refine ⟨47905760113098292996242733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63874346817464390661656977 47905760113098292996242733)
              ·
                refine ⟨17964660042411859873591025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47905760113098292996242733 17964660042411859873591025)
                ·
                  refine ⟨13473495031808894905193269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17964660042411859873591025 13473495031808894905193269)
                  ·
                    refine ⟨1263140159232083897361869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13473495031808894905193269 1263140159232083897361869)
                    ·
                      rfl

theorem cell22_3689935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_3689935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689935 prefixEnd_3689935 := by exact prefixLift 3689935
  have htrace : WordTrace (prefixWord ++ tailWord_3689935) baseStart_3689935 baseEnd_3689935 := by
    simpa [prefixWord, tailWord_3689935, baseEnd_3689935] using wordTrace_append hprefix tailTrace_3689935
  have hstable : (prefixWord ++ tailWord_3689935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689935).length < 2 ^ (prefixWord ++ tailWord_3689935).sum := by decide
  have hdescent : baseEnd_3689935 < baseStart_3689935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3689967 : List Nat := [1, 1, 2, 1, 4, 1, 2, 5, 1, 4]
def baseStart_3689967 : Nat := 118140960795 + 3689967 * 2 ^ 59
def prefixEnd_3689967 : Nat := 4983230072969 + 3 ^ 40 * 3689967 * 2
def baseEnd_3689967 : Nat := 1263151113486046480561771

theorem tailTrace_3689967 : CollatzResearch.WordTrace tailWord_3689967 prefixEnd_3689967 1263151113486046480561771 := by
  unfold tailWord_3689967
  simp only [CollatzResearch.WordTrace]
  refine ⟨134584153022887230036228155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89722768681924820024152103 134584153022887230036228155)
  ·
    refine ⟨201876229534330845054342233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134584153022887230036228155 201876229534330845054342233)
    ·
      refine ⟨151407172150748133790756675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201876229534330845054342233 151407172150748133790756675)
      ·
        refine ⟨227110758226122200686135013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151407172150748133790756675 227110758226122200686135013)
        ·
          refine ⟨42583267167397912628650315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 227110758226122200686135013 42583267167397912628650315)
          ·
            refine ⟨63874900751096868942975473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42583267167397912628650315 63874900751096868942975473)
            ·
              refine ⟨47906175563322651707231605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63874900751096868942975473 47906175563322651707231605)
              ·
                refine ⟨4491203959061498597552963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47906175563322651707231605 4491203959061498597552963)
                ·
                  refine ⟨6736805938592247896329445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491203959061498597552963 6736805938592247896329445)
                  ·
                    refine ⟨1263151113486046480561771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6736805938592247896329445 1263151113486046480561771)
                    ·
                      rfl

theorem cell22_3689967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 4].length) (baseStart_3689967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3689967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3689967 prefixEnd_3689967 := by exact prefixLift 3689967
  have htrace : WordTrace (prefixWord ++ tailWord_3689967) baseStart_3689967 baseEnd_3689967 := by
    simpa [prefixWord, tailWord_3689967, baseEnd_3689967] using wordTrace_append hprefix tailTrace_3689967
  have hstable : (prefixWord ++ tailWord_3689967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3689967).length < 2 ^ (prefixWord ++ tailWord_3689967).sum := by decide
  have hdescent : baseEnd_3689967 < baseStart_3689967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3689967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690012 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 1, 6]
def baseStart_3690012 : Nat := 118140960795 + 3690012 * 2 ^ 59
def prefixEnd_3690012 : Nat := 4983230072969 + 3 ^ 40 * 3690012 * 2
def baseEnd_3690012 : Nat := 1263166517905681363186633

theorem tailTrace_3690012 : CollatzResearch.WordTrace tailWord_3690012 prefixEnd_3690012 1263166517905681363186633 := by
  unfold tailWord_3690012
  simp only [CollatzResearch.WordTrace]
  refine ⟨67292897153862101360808145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89723862871816135147744193 67292897153862101360808145)
  ·
    refine ⟨50469672865396576020606109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67292897153862101360808145 50469672865396576020606109)
    ·
      refine ⟨18926127324523716007727291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50469672865396576020606109 18926127324523716007727291)
      ·
        refine ⟨28389190986785574011590937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18926127324523716007727291 28389190986785574011590937)
        ·
          refine ⟨21291893240089180508693203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28389190986785574011590937 21291893240089180508693203)
          ·
            refine ⟨31937839860133770763039805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21291893240089180508693203 31937839860133770763039805)
            ·
              refine ⟨11976689947550164036139927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31937839860133770763039805 11976689947550164036139927)
              ·
                refine ⟨17965034921325246054209891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11976689947550164036139927 17965034921325246054209891)
                ·
                  refine ⟨26947552381987869081314837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17965034921325246054209891 26947552381987869081314837)
                  ·
                    refine ⟨1263166517905681363186633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26947552381987869081314837 1263166517905681363186633)
                    ·
                      rfl

theorem cell22_3690012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_3690012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690012 prefixEnd_3690012 := by exact prefixLift 3690012
  have htrace : WordTrace (prefixWord ++ tailWord_3690012) baseStart_3690012 baseEnd_3690012 := by
    simpa [prefixWord, tailWord_3690012, baseEnd_3690012] using wordTrace_append hprefix tailTrace_3690012
  have hstable : (prefixWord ++ tailWord_3690012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690012).length < 2 ^ (prefixWord ++ tailWord_3690012).sum := by decide
  have hdescent : baseEnd_3690012 < baseStart_3690012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690016 : List Nat := [2, 1, 1, 6, 1, 2, 2, 3, 4]
def baseStart_3690016 : Nat := 118140960795 + 3690016 * 2 ^ 59
def prefixEnd_3690016 : Nat := 4983230072969 + 3 ^ 40 * 3690016 * 2
def baseEnd_3690016 : Nat := 421055962395808895362207

theorem tailTrace_3690016 : CollatzResearch.WordTrace tailWord_3690016 prefixEnd_3690016 421055962395808895362207 := by
  unfold tailWord_3690016
  simp only [CollatzResearch.WordTrace]
  refine ⟨67292970099854855702380951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89723960133139807603174601 67292970099854855702380951)
  ·
    refine ⟨100939455149782283553571427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67292970099854855702380951 100939455149782283553571427)
    ·
      refine ⟨151409182724673425330357141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100939455149782283553571427 151409182724673425330357141)
      ·
        refine ⟨7097305440219066812360491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 151409182724673425330357141 7097305440219066812360491)
        ·
          refine ⟨10645958160328600218540737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7097305440219066812360491 10645958160328600218540737)
          ·
            refine ⟨7984468620246450163905553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10645958160328600218540737 7984468620246450163905553)
            ·
              refine ⟨5988351465184837622929165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7984468620246450163905553 5988351465184837622929165)
              ·
                refine ⟨2245631799444314108598437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5988351465184837622929165 2245631799444314108598437)
                ·
                  refine ⟨421055962395808895362207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2245631799444314108598437 421055962395808895362207)
                  ·
                    rfl

theorem cell22_3690016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 3, 4].length) (baseStart_3690016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690016 prefixEnd_3690016 := by exact prefixLift 3690016
  have htrace : WordTrace (prefixWord ++ tailWord_3690016) baseStart_3690016 baseEnd_3690016 := by
    simpa [prefixWord, tailWord_3690016, baseEnd_3690016] using wordTrace_append hprefix tailTrace_3690016
  have hstable : (prefixWord ++ tailWord_3690016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690016).length < 2 ^ (prefixWord ++ tailWord_3690016).sum := by decide
  have hdescent : baseEnd_3690016 < baseStart_3690016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690087 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 4, 5]
def baseStart_3690087 : Nat := 118140960795 + 3690087 * 2 ^ 59
def prefixEnd_3690087 : Nat := 4983230072969 + 3 ^ 40 * 3690087 * 2
def baseEnd_3690087 : Nat := 1263192191938406167561403

theorem tailTrace_3690087 : CollatzResearch.WordTrace tailWord_3690087 prefixEnd_3690087 1263192191938406167561403 := by
  unfold tailWord_3690087
  simp only [CollatzResearch.WordTrace]
  refine ⟨134588529782452490530596515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89725686521634993687064343 134588529782452490530596515)
  ·
    refine ⟨201882794673678735795894773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134588529782452490530596515 201882794673678735795894773)
    ·
      refine ⟨18926512000657381480865135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 201882794673678735795894773 18926512000657381480865135)
      ·
        refine ⟨28389768000986072221297703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18926512000657381480865135 28389768000986072221297703)
        ·
          refine ⟨42584652001479108331946555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28389768000986072221297703 42584652001479108331946555)
          ·
            refine ⟨63876978002218662497919833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42584652001479108331946555 63876978002218662497919833)
            ·
              refine ⟨47907733501663996873439875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63876978002218662497919833 47907733501663996873439875)
              ·
                refine ⟨71861600252495995310159813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47907733501663996873439875 71861600252495995310159813)
                ·
                  refine ⟨13474050047342999120654965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71861600252495995310159813 13474050047342999120654965)
                  ·
                    refine ⟨1263192191938406167561403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13474050047342999120654965 1263192191938406167561403)
                    ·
                      rfl

theorem cell22_3690087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_3690087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690087 prefixEnd_3690087 := by exact prefixLift 3690087
  have htrace : WordTrace (prefixWord ++ tailWord_3690087) baseStart_3690087 baseEnd_3690087 := by
    simpa [prefixWord, tailWord_3690087, baseEnd_3690087] using wordTrace_append hprefix tailTrace_3690087
  have hstable : (prefixWord ++ tailWord_3690087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690087).length < 2 ^ (prefixWord ++ tailWord_3690087).sum := by decide
  have hdescent : baseEnd_3690087 < baseStart_3690087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690093 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_3690093 : Nat := 118140960795 + 3690093 * 2 ^ 59
def prefixEnd_3690093 : Nat := 4983230072969 + 3 ^ 40 * 3690093 * 2
def baseEnd_3690093 : Nat := 1263194245861024151911385

theorem tailTrace_3690093 : CollatzResearch.WordTrace tailWord_3690093 prefixEnd_3690093 1263194245861024151911385 := by
  unfold tailWord_3690093
  simp only [CollatzResearch.WordTrace]
  refine ⟨134588748620430753555314933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89725832413620502370209955 134588748620430753555314933)
  ·
    refine ⟨12617695183165383145810775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134588748620430753555314933 12617695183165383145810775)
    ·
      refine ⟨18926542774748074718716163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12617695183165383145810775 18926542774748074718716163)
      ·
        refine ⟨28389814162122112078074245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18926542774748074718716163 28389814162122112078074245)
        ·
          refine ⟨5323090155397896014638921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28389814162122112078074245 5323090155397896014638921)
          ·
            refine ⟨3992317616548422010979191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5323090155397896014638921 3992317616548422010979191)
            ·
              refine ⟨5988476424822633016468787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992317616548422010979191 5988476424822633016468787)
              ·
                refine ⟨8982714637233949524703181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5988476424822633016468787 8982714637233949524703181)
                ·
                  refine ⟨3368517988962731071763693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8982714637233949524703181 3368517988962731071763693)
                  ·
                    refine ⟨1263194245861024151911385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3368517988962731071763693 1263194245861024151911385)
                    ·
                      rfl

theorem cell22_3690093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_3690093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690093 prefixEnd_3690093 := by exact prefixLift 3690093
  have htrace : WordTrace (prefixWord ++ tailWord_3690093) baseStart_3690093 baseEnd_3690093 := by
    simpa [prefixWord, tailWord_3690093, baseEnd_3690093] using wordTrace_append hprefix tailTrace_3690093
  have hstable : (prefixWord ++ tailWord_3690093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690093).length < 2 ^ (prefixWord ++ tailWord_3690093).sum := by decide
  have hdescent : baseEnd_3690093 < baseStart_3690093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690117 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 8]
def baseStart_3690117 : Nat := 118140960795 + 3690117 * 2 ^ 59
def prefixEnd_3690117 : Nat := 4983230072969 + 3 ^ 40 * 3690117 * 2
def baseEnd_3690117 : Nat := 421067487183832029770437

theorem tailTrace_3690117 : CollatzResearch.WordTrace tailWord_3690117 prefixEnd_3690117 421067487183832029770437 := by
  unfold tailWord_3690117
  simp only [CollatzResearch.WordTrace]
  refine ⟨134589623972343805654188605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89726415981562537102792403 134589623972343805654188605)
  ·
    refine ⟨50471108989628927120320727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134589623972343805654188605 50471108989628927120320727)
    ·
      refine ⟨75706663484443390680481091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50471108989628927120320727 75706663484443390680481091)
      ·
        refine ⟨113559995226665086020721637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75706663484443390680481091 113559995226665086020721637)
        ·
          refine ⟨21292499104999703628885307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113559995226665086020721637 21292499104999703628885307)
          ·
            refine ⟨31938748657499555443327961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21292499104999703628885307 31938748657499555443327961)
            ·
              refine ⟨23954061493124666582495971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31938748657499555443327961 23954061493124666582495971)
              ·
                refine ⟨35931092239686999873743957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23954061493124666582495971 35931092239686999873743957)
                ·
                  refine ⟨421067487183832029770437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35931092239686999873743957 421067487183832029770437)
                  ·
                    rfl

theorem cell22_3690117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 8].length) (baseStart_3690117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690117 prefixEnd_3690117 := by exact prefixLift 3690117
  have htrace : WordTrace (prefixWord ++ tailWord_3690117) baseStart_3690117 baseEnd_3690117 := by
    simpa [prefixWord, tailWord_3690117, baseEnd_3690117] using wordTrace_append hprefix tailTrace_3690117
  have hstable : (prefixWord ++ tailWord_3690117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690117).length < 2 ^ (prefixWord ++ tailWord_3690117).sum := by decide
  have hdescent : baseEnd_3690117 < baseStart_3690117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690119 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 3, 4]
def baseStart_3690119 : Nat := 118140960795 + 3690119 * 2 ^ 59
def prefixEnd_3690119 : Nat := 4983230072969 + 3 ^ 40 * 3690119 * 2
def baseEnd_3690119 : Nat := 1263203146192368750761305

theorem tailTrace_3690119 : CollatzResearch.WordTrace tailWord_3690119 prefixEnd_3690119 1263203146192368750761305 := by
  unfold tailWord_3690119
  simp only [CollatzResearch.WordTrace]
  refine ⟨134589696918336559995761411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89726464612224373330507607 134589696918336559995761411)
  ·
    refine ⟨201884545377504839993642117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134589696918336559995761411 201884545377504839993642117)
    ·
      refine ⟨37853352258282157498807897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201884545377504839993642117 37853352258282157498807897)
      ·
        refine ⟨28390014193711618124105923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37853352258282157498807897 28390014193711618124105923)
        ·
          refine ⟨42585021290567427186158885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28390014193711618124105923 42585021290567427186158885)
          ·
            refine ⟨7984691491981392597404791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42585021290567427186158885 7984691491981392597404791)
            ·
              refine ⟨11977037237972088896107187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7984691491981392597404791 11977037237972088896107187)
              ·
                refine ⟨17965555856958133344160781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11977037237972088896107187 17965555856958133344160781)
                ·
                  refine ⟨6737083446359300004060293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17965555856958133344160781 6737083446359300004060293)
                  ·
                    refine ⟨1263203146192368750761305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6737083446359300004060293 1263203146192368750761305)
                    ·
                      rfl

theorem cell22_3690119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_3690119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690119 prefixEnd_3690119 := by exact prefixLift 3690119
  have htrace : WordTrace (prefixWord ++ tailWord_3690119) baseStart_3690119 baseEnd_3690119 := by
    simpa [prefixWord, tailWord_3690119, baseEnd_3690119] using wordTrace_append hprefix tailTrace_3690119
  have hstable : (prefixWord ++ tailWord_3690119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690119).length < 2 ^ (prefixWord ++ tailWord_3690119).sum := by decide
  have hdescent : baseEnd_3690119 < baseStart_3690119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690149 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 4, 3]
def baseStart_3690149 : Nat := 118140960795 + 3690149 * 2 ^ 59
def prefixEnd_3690149 : Nat := 4983230072969 + 3 ^ 40 * 3690149 * 2
def baseEnd_3690149 : Nat := 1263213415805458672511213

theorem tailTrace_3690149 : CollatzResearch.WordTrace tailWord_3690149 prefixEnd_3690149 1263213415805458672511213 := by
  unfold tailWord_3690149
  simp only [CollatzResearch.WordTrace]
  refine ⟨134590791108227875119353501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89727194072151916746235667 134590791108227875119353501)
  ·
    refine ⟨50471546665585453169757563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134590791108227875119353501 50471546665585453169757563)
    ·
      refine ⟨75707319998378179754636345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50471546665585453169757563 75707319998378179754636345)
      ·
        refine ⟨56780489998783634815977259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75707319998378179754636345 56780489998783634815977259)
        ·
          refine ⟨85170734998175452223965889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56780489998783634815977259 85170734998175452223965889)
          ·
            refine ⟨63878051248631589167974417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85170734998175452223965889 63878051248631589167974417)
            ·
              refine ⟨47908538436473691875980813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63878051248631589167974417 47908538436473691875980813)
              ·
                refine ⟨17965701913677634453492805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47908538436473691875980813 17965701913677634453492805)
                ·
                  refine ⟨3368569108814556460029901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17965701913677634453492805 3368569108814556460029901)
                  ·
                    refine ⟨1263213415805458672511213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3368569108814556460029901 1263213415805458672511213)
                    ·
                      rfl

theorem cell22_3690149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_3690149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690149 prefixEnd_3690149 := by exact prefixLift 3690149
  have htrace : WordTrace (prefixWord ++ tailWord_3690149) baseStart_3690149 baseEnd_3690149 := by
    simpa [prefixWord, tailWord_3690149, baseEnd_3690149] using wordTrace_append hprefix tailTrace_3690149
  have hstable : (prefixWord ++ tailWord_3690149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690149).length < 2 ^ (prefixWord ++ tailWord_3690149).sum := by decide
  have hdescent : baseEnd_3690149 < baseStart_3690149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690192 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 1, 8]
def baseStart_3690192 : Nat := 118140960795 + 3690192 * 2 ^ 59
def prefixEnd_3690192 : Nat := 4983230072969 + 3 ^ 40 * 3690192 * 2
def baseEnd_3690192 : Nat := 1263228135584220893686081

theorem tailTrace_3690192 : CollatzResearch.WordTrace tailWord_3690192 prefixEnd_3690192 1263228135584220893686081 := by
  unfold tailWord_3690192
  simp only [CollatzResearch.WordTrace]
  refine ⟨67296179723536046731584415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89728239631381395642112553 67296179723536046731584415)
  ·
    refine ⟨100944269585304070097376623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67296179723536046731584415 100944269585304070097376623)
    ·
      refine ⟨151416404377956105146064935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100944269585304070097376623 151416404377956105146064935)
      ·
        refine ⟨227124606566934157719097403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151416404377956105146064935 227124606566934157719097403)
        ·
          refine ⟨340686909850401236578646105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227124606566934157719097403 340686909850401236578646105)
          ·
            refine ⟨255515182387800927433984579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340686909850401236578646105 255515182387800927433984579)
            ·
              refine ⟨383272773581701391150976869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 255515182387800927433984579 383272773581701391150976869)
              ·
                refine ⟨71863645046569010840808163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 383272773581701391150976869 71863645046569010840808163)
                ·
                  refine ⟨107795467569853516261212245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71863645046569010840808163 107795467569853516261212245)
                  ·
                    refine ⟨1263228135584220893686081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107795467569853516261212245 1263228135584220893686081)
                    ·
                      rfl

theorem cell22_3690192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_3690192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690192 prefixEnd_3690192 := by exact prefixLift 3690192
  have htrace : WordTrace (prefixWord ++ tailWord_3690192) baseStart_3690192 baseEnd_3690192 := by
    simpa [prefixWord, tailWord_3690192, baseEnd_3690192] using wordTrace_append hprefix tailTrace_3690192
  have hstable : (prefixWord ++ tailWord_3690192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690192).length < 2 ^ (prefixWord ++ tailWord_3690192).sum := by decide
  have hdescent : baseEnd_3690192 < baseStart_3690192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690301 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 3, 5]
def baseStart_3690301 : Nat := 118140960795 + 3690301 * 2 ^ 59
def prefixEnd_3690301 : Nat := 4983230072969 + 3 ^ 40 * 3690301 * 2
def baseEnd_3690301 : Nat := 1263265448511780942710747

theorem tailTrace_3690301 : CollatzResearch.WordTrace tailWord_3690301 prefixEnd_3690301 1263265448511780942710747 := by
  unfold tailWord_3690301
  simp only [CollatzResearch.WordTrace]
  refine ⟨134596335003677205078886757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89730890002451470052591171 134596335003677205078886757)
  ·
    refine ⟨25236812813189475952291267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134596335003677205078886757 25236812813189475952291267)
    ·
      refine ⟨37855219219784213928436901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25236812813189475952291267 37855219219784213928436901)
      ·
        refine ⟨7097853603709540111581919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37855219219784213928436901 7097853603709540111581919)
        ·
          refine ⟨10646780405564310167372879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7097853603709540111581919 10646780405564310167372879)
          ·
            refine ⟨15970170608346465251059319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10646780405564310167372879 15970170608346465251059319)
            ·
              refine ⟨23955255912519697876588979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15970170608346465251059319 23955255912519697876588979)
              ·
                refine ⟨35932883868779546814883469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23955255912519697876588979 35932883868779546814883469)
                ·
                  refine ⟨13474831450792330055581301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35932883868779546814883469 13474831450792330055581301)
                  ·
                    refine ⟨1263265448511780942710747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13474831450792330055581301 1263265448511780942710747)
                    ·
                      rfl

theorem cell22_3690301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_3690301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690301 prefixEnd_3690301 := by exact prefixLift 3690301
  have htrace : WordTrace (prefixWord ++ tailWord_3690301) baseStart_3690301 baseEnd_3690301 := by
    simpa [prefixWord, tailWord_3690301, baseEnd_3690301] using wordTrace_append hprefix tailTrace_3690301
  have hstable : (prefixWord ++ tailWord_3690301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690301).length < 2 ^ (prefixWord ++ tailWord_3690301).sum := by decide
  have hdescent : baseEnd_3690301 < baseStart_3690301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690350 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 2, 4]
def baseStart_3690350 : Nat := 118140960795 + 3690350 * 2 ^ 59
def prefixEnd_3690350 : Nat := 4983230072969 + 3 ^ 40 * 3690350 * 2
def baseEnd_3690350 : Nat := 1263282222213161148235597

theorem tailTrace_3690350 : CollatzResearch.WordTrace tailWord_3690350 prefixEnd_3690350 1263282222213161148235597 := by
  unfold tailWord_3690350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16824765272562460805927563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89732081453666457631613669 16824765272562460805927563)
  ·
    refine ⟨25237147908843691208891345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16824765272562460805927563 25237147908843691208891345)
    ·
      refine ⟨18927860931632768406668509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25237147908843691208891345 18927860931632768406668509)
      ·
        refine ⟨7097947849362288152500691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18927860931632768406668509 7097947849362288152500691)
        ·
          refine ⟨10646921774043432228751037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7097947849362288152500691 10646921774043432228751037)
          ·
            refine ⟨3992595665266287085781639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10646921774043432228751037 3992595665266287085781639)
            ·
              refine ⟨5988893497899430628672459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992595665266287085781639 5988893497899430628672459)
              ·
                refine ⟨8983340246849145943008689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5988893497899430628672459 8983340246849145943008689)
                ·
                  refine ⟨6737505185136859457256517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8983340246849145943008689 6737505185136859457256517)
                  ·
                    refine ⟨1263282222213161148235597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6737505185136859457256517 1263282222213161148235597)
                    ·
                      rfl

theorem cell22_3690350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_3690350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690350 prefixEnd_3690350 := by exact prefixLift 3690350
  have htrace : WordTrace (prefixWord ++ tailWord_3690350) baseStart_3690350 baseEnd_3690350 := by
    simpa [prefixWord, tailWord_3690350, baseEnd_3690350] using wordTrace_append hprefix tailTrace_3690350
  have hstable : (prefixWord ++ tailWord_3690350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690350).length < 2 ^ (prefixWord ++ tailWord_3690350).sum := by decide
  have hdescent : baseEnd_3690350 < baseStart_3690350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690369 : List Nat := [1, 2, 4, 4, 2, 1, 1, 2, 2, 3]
def baseStart_3690369 : Nat := 118140960795 + 3690369 * 2 ^ 59
def prefixEnd_3690369 : Nat := 4983230072969 + 3 ^ 40 * 3690369 * 2
def baseEnd_3690369 : Nat := 1263288726301451432010539

theorem tailTrace_3690369 : CollatzResearch.WordTrace tailWord_3690369 prefixEnd_3690369 1263288726301451432010539 := by
  unfold tailWord_3690369
  simp only [CollatzResearch.WordTrace]
  refine ⟨134598815167430852692362161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89732543444953901794908107 134598815167430852692362161)
  ·
    refine ⟨100949111375573139519271621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134598815167430852692362161 100949111375573139519271621)
    ·
      refine ⟨18927958382919963659863429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100949111375573139519271621 18927958382919963659863429)
      ·
        refine ⟨3548992196797493186224393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18927958382919963659863429 3548992196797493186224393)
        ·
          refine ⟨2661744147598119889668295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3548992196797493186224393 2661744147598119889668295)
          ·
            refine ⟨3992616221397179834502443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661744147598119889668295 3992616221397179834502443)
            ·
              refine ⟨5988924332095769751753665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992616221397179834502443 5988924332095769751753665)
              ·
                refine ⟨4491693249071827313815249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5988924332095769751753665 4491693249071827313815249)
                ·
                  refine ⟨3368769936803870485361437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4491693249071827313815249 3368769936803870485361437)
                  ·
                    refine ⟨1263288726301451432010539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3368769936803870485361437 1263288726301451432010539)
                    ·
                      rfl

theorem cell22_3690369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_3690369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690369 prefixEnd_3690369 := by exact prefixLift 3690369
  have htrace : WordTrace (prefixWord ++ tailWord_3690369) baseStart_3690369 baseEnd_3690369 := by
    simpa [prefixWord, tailWord_3690369, baseEnd_3690369] using wordTrace_append hprefix tailTrace_3690369
  have hstable : (prefixWord ++ tailWord_3690369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690369).length < 2 ^ (prefixWord ++ tailWord_3690369).sum := by decide
  have hdescent : baseEnd_3690369 < baseStart_3690369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690391 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 2, 5]
def baseStart_3690391 : Nat := 118140960795 + 3690391 * 2 ^ 59
def prefixEnd_3690391 : Nat := 4983230072969 + 3 ^ 40 * 3690391 * 2
def baseEnd_3690391 : Nat := 1263296257351050707960471

theorem tailTrace_3690391 : CollatzResearch.WordTrace tailWord_3690391 prefixEnd_3690391 1263296257351050707960471 := by
  unfold tailWord_3690391
  simp only [CollatzResearch.WordTrace]
  refine ⟨134599617573351150449663027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89733078382234100299775351 134599617573351150449663027)
  ·
    refine ⟨201899426360026725674494541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134599617573351150449663027 201899426360026725674494541)
    ·
      refine ⟨75712284885010022127935453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 201899426360026725674494541 75712284885010022127935453)
      ·
        refine ⟨28392106831878758297975795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75712284885010022127935453 28392106831878758297975795)
        ·
          refine ⟨42588160247818137446963693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28392106831878758297975795 42588160247818137446963693)
          ·
            refine ⟨15970560092931801542611385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42588160247818137446963693 15970560092931801542611385)
            ·
              refine ⟨11977920069698851156958539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15970560092931801542611385 11977920069698851156958539)
              ·
                refine ⟨17966880104548276735437809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11977920069698851156958539 17966880104548276735437809)
                ·
                  refine ⟨13475160078411207551578357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17966880104548276735437809 13475160078411207551578357)
                  ·
                    refine ⟨1263296257351050707960471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13475160078411207551578357 1263296257351050707960471)
                    ·
                      rfl

theorem cell22_3690391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_3690391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690391 prefixEnd_3690391 := by exact prefixLift 3690391
  have htrace : WordTrace (prefixWord ++ tailWord_3690391) baseStart_3690391 baseEnd_3690391 := by
    simpa [prefixWord, tailWord_3690391, baseEnd_3690391] using wordTrace_append hprefix tailTrace_3690391
  have hstable : (prefixWord ++ tailWord_3690391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690391).length < 2 ^ (prefixWord ++ tailWord_3690391).sum := by decide
  have hdescent : baseEnd_3690391 < baseStart_3690391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690457 : List Nat := [1, 2, 1, 2, 7, 1, 1, 2, 1, 4]
def baseStart_3690457 : Nat := 118140960795 + 3690457 * 2 ^ 59
def prefixEnd_3690457 : Nat := 4983230072969 + 3 ^ 40 * 3690457 * 2
def baseEnd_3690457 : Nat := 1263318850499848535810269

theorem tailTrace_3690457 : CollatzResearch.WordTrace tailWord_3690457 prefixEnd_3690457 1263318850499848535810269 := by
  unfold tailWord_3690457
  simp only [CollatzResearch.WordTrace]
  refine ⟨134602024791112043721565625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89734683194074695814377083 134602024791112043721565625)
  ·
    refine ⟨100951518593334032791174219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134602024791112043721565625 100951518593334032791174219)
    ·
      refine ⟨151427277890001049186761329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100951518593334032791174219 151427277890001049186761329)
      ·
        refine ⟨113570458417500786890070997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151427277890001049186761329 113570458417500786890070997)
        ·
          refine ⟨2661807619160174692736039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 113570458417500786890070997 2661807619160174692736039)
          ·
            refine ⟨3992711428740262039104059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2661807619160174692736039 3992711428740262039104059)
            ·
              refine ⟨5989067143110393058656089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992711428740262039104059 5989067143110393058656089)
              ·
                refine ⟨4491800357332794793992067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5989067143110393058656089 4491800357332794793992067)
                ·
                  refine ⟨6737700535999192190988101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491800357332794793992067 6737700535999192190988101)
                  ·
                    refine ⟨1263318850499848535810269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6737700535999192190988101 1263318850499848535810269)
                    ·
                      rfl

theorem cell22_3690457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 1, 4].length) (baseStart_3690457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690457 prefixEnd_3690457 := by exact prefixLift 3690457
  have htrace : WordTrace (prefixWord ++ tailWord_3690457) baseStart_3690457 baseEnd_3690457 := by
    simpa [prefixWord, tailWord_3690457, baseEnd_3690457] using wordTrace_append hprefix tailTrace_3690457
  have hstable : (prefixWord ++ tailWord_3690457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690457).length < 2 ^ (prefixWord ++ tailWord_3690457).sum := by decide
  have hdescent : baseEnd_3690457 < baseStart_3690457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690468 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_3690468 : Nat := 118140960795 + 3690468 * 2 ^ 59
def prefixEnd_3690468 : Nat := 4983230072969 + 3 ^ 40 * 3690468 * 2
def baseEnd_3690468 : Nat := 1263322616024648173785235

theorem tailTrace_3690468 : CollatzResearch.WordTrace tailWord_3690468 prefixEnd_3690468 1263322616024648173785235 := by
  unfold tailWord_3690468
  simp only [CollatzResearch.WordTrace]
  refine ⟨67301212997036096300108029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89734950662714795066810705 67301212997036096300108029)
  ·
    refine ⟨25237954873888536112540511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67301212997036096300108029 25237954873888536112540511)
    ·
      refine ⟨37856932310832804168810767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25237954873888536112540511 37856932310832804168810767)
      ·
        refine ⟨56785398466249206253216151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37856932310832804168810767 56785398466249206253216151)
        ·
          refine ⟨85178097699373809379824227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56785398466249206253216151 85178097699373809379824227)
          ·
            refine ⟨127767146549060714069736341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85178097699373809379824227 127767146549060714069736341)
            ·
              refine ⟨5989084994487220972018891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127767146549060714069736341 5989084994487220972018891)
              ·
                refine ⟨8983627491730831458028337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5989084994487220972018891 8983627491730831458028337)
                ·
                  refine ⟨6737720618798123593521253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8983627491730831458028337 6737720618798123593521253)
                  ·
                    refine ⟨1263322616024648173785235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6737720618798123593521253 1263322616024648173785235)
                    ·
                      rfl

theorem cell22_3690468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_3690468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690468 prefixEnd_3690468 := by exact prefixLift 3690468
  have htrace : WordTrace (prefixWord ++ tailWord_3690468) baseStart_3690468 baseEnd_3690468 := by
    simpa [prefixWord, tailWord_3690468, baseEnd_3690468] using wordTrace_append hprefix tailTrace_3690468
  have hstable : (prefixWord ++ tailWord_3690468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690468).length < 2 ^ (prefixWord ++ tailWord_3690468).sum := by decide
  have hdescent : baseEnd_3690468 < baseStart_3690468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690545 : List Nat := [1, 2, 2, 3, 1, 5, 1, 2, 5]
def baseStart_3690545 : Nat := 118140960795 + 3690545 * 2 ^ 59
def prefixEnd_3690545 : Nat := 4983230072969 + 3 ^ 40 * 3690545 * 2
def baseEnd_3690545 : Nat := 421116324899415213203333

theorem tailTrace_3690545 : CollatzResearch.WordTrace tailWord_3690545 prefixEnd_3690545 421116324899415213203333 := by
  unfold tailWord_3690545
  simp only [CollatzResearch.WordTrace]
  refine ⟨134605234414793234750769089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89736822943195489833846059 134605234414793234750769089)
  ·
    refine ⟨100953925811094926063076817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134605234414793234750769089 100953925811094926063076817)
    ·
      refine ⟨75715444358321194547307613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100953925811094926063076817 75715444358321194547307613)
      ·
        refine ⟨28393291634370447955240355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75715444358321194547307613 28393291634370447955240355)
        ·
          refine ⟨42589937451555671932860533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28393291634370447955240355 42589937451555671932860533)
          ·
            refine ⟨3992806636083344243705675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42589937451555671932860533 3992806636083344243705675)
            ·
              refine ⟨5989209954125016365558513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3992806636083344243705675 5989209954125016365558513)
              ·
                refine ⟨4491907465593762274168885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5989209954125016365558513 4491907465593762274168885)
                ·
                  refine ⟨421116324899415213203333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4491907465593762274168885 421116324899415213203333)
                  ·
                    rfl

theorem cell22_3690545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 5].length) (baseStart_3690545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690545 prefixEnd_3690545 := by exact prefixLift 3690545
  have htrace : WordTrace (prefixWord ++ tailWord_3690545) baseStart_3690545 baseEnd_3690545 := by
    simpa [prefixWord, tailWord_3690545, baseEnd_3690545] using wordTrace_append hprefix tailTrace_3690545
  have hstable : (prefixWord ++ tailWord_3690545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690545).length < 2 ^ (prefixWord ++ tailWord_3690545).sum := by decide
  have hdescent : baseEnd_3690545 < baseStart_3690545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690605 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 4, 3]
def baseStart_3690605 : Nat := 118140960795 + 3690605 * 2 ^ 59
def prefixEnd_3690605 : Nat := 4983230072969 + 3 ^ 40 * 3690605 * 2
def baseEnd_3690605 : Nat := 1263369513924425483109815

theorem tailTrace_3690605 : CollatzResearch.WordTrace tailWord_3690605 prefixEnd_3690605 1263369513924425483109815 := by
  unfold tailWord_3690605
  simp only [CollatzResearch.WordTrace]
  refine ⟨134607422794575864997953269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89738281863050576665302179 134607422794575864997953269)
  ·
    refine ⟨12619445886991487343558119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 134607422794575864997953269 12619445886991487343558119)
    ·
      refine ⟨18929168830487231015337179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12619445886991487343558119 18929168830487231015337179)
      ·
        refine ⟨28393753245730846523005769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18929168830487231015337179 28393753245730846523005769)
        ·
          refine ⟨21295314934298134892254327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28393753245730846523005769 21295314934298134892254327)
          ·
            refine ⟨31942972401447202338381491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21295314934298134892254327 31942972401447202338381491)
            ·
              refine ⟨47914458602170803507572237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31942972401447202338381491 47914458602170803507572237)
              ·
                refine ⟨17967921975814051315339589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47914458602170803507572237 17967921975814051315339589)
                ·
                  refine ⟨3368985370465134621626173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17967921975814051315339589 3368985370465134621626173)
                  ·
                    refine ⟨1263369513924425483109815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3368985370465134621626173 1263369513924425483109815)
                    ·
                      rfl

theorem cell22_3690605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_3690605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690605 prefixEnd_3690605 := by exact prefixLift 3690605
  have htrace : WordTrace (prefixWord ++ tailWord_3690605) baseStart_3690605 baseEnd_3690605 := by
    simpa [prefixWord, tailWord_3690605, baseEnd_3690605] using wordTrace_append hprefix tailTrace_3690605
  have hstable : (prefixWord ++ tailWord_3690605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690605).length < 2 ^ (prefixWord ++ tailWord_3690605).sum := by decide
  have hdescent : baseEnd_3690605 < baseStart_3690605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690607 : List Nat := [1, 1, 2, 1, 3, 5, 3, 2, 4]
def baseStart_3690607 : Nat := 118140960795 + 3690607 * 2 ^ 59
def prefixEnd_3690607 : Nat := 4983230072969 + 3 ^ 40 * 3690607 * 2
def baseEnd_3690607 : Nat := 421123399521766048186603

theorem tailTrace_3690607 : CollatzResearch.WordTrace tailWord_3690607 prefixEnd_3690607 421123399521766048186603 := by
  unfold tailWord_3690607
  simp only [CollatzResearch.WordTrace]
  refine ⟨134607495740568619339526075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89738330493712412893017383 134607495740568619339526075)
  ·
    refine ⟨201911243610852929009289113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134607495740568619339526075 201911243610852929009289113)
    ·
      refine ⟨151433432708139696756966835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201911243610852929009289113 151433432708139696756966835)
      ·
        refine ⟨227150149062209545135450253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151433432708139696756966835 227150149062209545135450253)
        ·
          refine ⟨85181305898328579425793845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227150149062209545135450253 85181305898328579425793845)
          ·
            refine ⟨7985747427968304321168173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85181305898328579425793845 7985747427968304321168173)
            ·
              refine ⟨2994655285488114120438065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7985747427968304321168173 2994655285488114120438065)
              ·
                refine ⟨2245991464116085590328549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2994655285488114120438065 2245991464116085590328549)
                ·
                  refine ⟨421123399521766048186603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2245991464116085590328549 421123399521766048186603)
                  ·
                    rfl

theorem cell22_3690607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 2, 4].length) (baseStart_3690607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690607 prefixEnd_3690607 := by exact prefixLift 3690607
  have htrace : WordTrace (prefixWord ++ tailWord_3690607) baseStart_3690607 baseEnd_3690607 := by
    simpa [prefixWord, tailWord_3690607, baseEnd_3690607] using wordTrace_append hprefix tailTrace_3690607
  have hstable : (prefixWord ++ tailWord_3690607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690607).length < 2 ^ (prefixWord ++ tailWord_3690607).sum := by decide
  have hdescent : baseEnd_3690607 < baseStart_3690607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690725 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 6]
def baseStart_3690725 : Nat := 118140960795 + 3690725 * 2 ^ 59
def prefixEnd_3690725 : Nat := 4983230072969 + 3 ^ 40 * 3690725 * 2
def baseEnd_3690725 : Nat := 421136864125595056703149

theorem tailTrace_3690725 : CollatzResearch.WordTrace tailWord_3690725 prefixEnd_3690725 421136864125595056703149 := by
  unfold tailWord_3690725
  simp only [CollatzResearch.WordTrace]
  refine ⟨134611799554141125492321629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89741199702760750328214419 134611799554141125492321629)
  ·
    refine ⟨50479424832802922059620611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134611799554141125492321629 50479424832802922059620611)
    ·
      refine ⟨75719137249204383089430917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50479424832802922059620611 75719137249204383089430917)
      ·
        refine ⟨14197338234225821829268297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75719137249204383089430917 14197338234225821829268297)
        ·
          refine ⟨10648003675669366371951223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14197338234225821829268297 10648003675669366371951223)
          ·
            refine ⟨15972005513504049557926835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10648003675669366371951223 15972005513504049557926835)
            ·
              refine ⟨23958008270256074336890253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15972005513504049557926835 23958008270256074336890253)
              ·
                refine ⟨8984253101346027876333845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23958008270256074336890253 8984253101346027876333845)
                ·
                  refine ⟨421136864125595056703149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8984253101346027876333845 421136864125595056703149)
                  ·
                    rfl

theorem cell22_3690725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 6].length) (baseStart_3690725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690725 prefixEnd_3690725 := by exact prefixLift 3690725
  have htrace : WordTrace (prefixWord ++ tailWord_3690725) baseStart_3690725 baseEnd_3690725 := by
    simpa [prefixWord, tailWord_3690725, baseEnd_3690725] using wordTrace_append hprefix tailTrace_3690725
  have hstable : (prefixWord ++ tailWord_3690725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690725).length < 2 ^ (prefixWord ++ tailWord_3690725).sum := by decide
  have hdescent : baseEnd_3690725 < baseStart_3690725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690755 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 2, 4]
def baseStart_3690755 : Nat := 118140960795 + 3690755 * 2 ^ 59
def prefixEnd_3690755 : Nat := 4983230072969 + 3 ^ 40 * 3690755 * 2
def baseEnd_3690755 : Nat := 1263420861989875091859355

theorem tailTrace_3690755 : CollatzResearch.WordTrace tailWord_3690755 prefixEnd_3690755 1263420861989875091859355 := by
  unfold tailWord_3690755
  simp only [CollatzResearch.WordTrace]
  refine ⟨134612893744032440615913719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89741929162688293743942479 134612893744032440615913719)
  ·
    refine ⟨201919340616048660923870579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134612893744032440615913719 201919340616048660923870579)
    ·
      refine ⟨302879010924072991385805869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201919340616048660923870579 302879010924072991385805869)
      ·
        refine ⟨113579629096527371769677201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302879010924072991385805869 113579629096527371769677201)
        ·
          refine ⟨85184721822395528827257901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113579629096527371769677201 85184721822395528827257901)
          ·
            refine ⟨31944270683398323310221713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85184721822395528827257901 31944270683398323310221713)
            ·
              refine ⟨23958203012548742482666285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31944270683398323310221713 23958203012548742482666285)
              ·
                refine ⟨8984326129705778430999857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23958203012548742482666285 8984326129705778430999857)
                ·
                  refine ⟨6738244597279333823249893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8984326129705778430999857 6738244597279333823249893)
                  ·
                    refine ⟨1263420861989875091859355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6738244597279333823249893 1263420861989875091859355)
                    ·
                      rfl

theorem cell22_3690755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 4].length) (baseStart_3690755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690755 prefixEnd_3690755 := by exact prefixLift 3690755
  have htrace : WordTrace (prefixWord ++ tailWord_3690755) baseStart_3690755 baseEnd_3690755 := by
    simpa [prefixWord, tailWord_3690755, baseEnd_3690755] using wordTrace_append hprefix tailTrace_3690755
  have hstable : (prefixWord ++ tailWord_3690755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690755).length < 2 ^ (prefixWord ++ tailWord_3690755).sum := by decide
  have hdescent : baseEnd_3690755 < baseStart_3690755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690832 : List Nat := [2, 1, 1, 1, 1, 7, 2, 2, 5]
def baseStart_3690832 : Nat := 118140960795 + 3690832 * 2 ^ 59
def prefixEnd_3690832 : Nat := 4983230072969 + 3 ^ 40 * 3690832 * 2
def baseEnd_3690832 : Nat := 421149073554490852561373

theorem tailTrace_3690832 : CollatzResearch.WordTrace tailWord_3690832 prefixEnd_3690832 421149073554490852561373 := by
  unfold tailWord_3690832
  simp only [CollatzResearch.WordTrace]
  refine ⟨67307851082376741383233375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89743801443168988510977833 67307851082376741383233375)
  ·
    refine ⟨100961776623565112074850063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67307851082376741383233375 100961776623565112074850063)
    ·
      refine ⟨151442664935347668112275095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100961776623565112074850063 151442664935347668112275095)
      ·
        refine ⟨227163997403021502168412643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151442664935347668112275095 227163997403021502168412643)
        ·
          refine ⟨340745996104532253252618965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227163997403021502168412643 340745996104532253252618965)
          ·
            refine ⟨7986234283699974685608257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 340745996104532253252618965 7986234283699974685608257)
            ·
              refine ⟨5989675712774981014206193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7986234283699974685608257 5989675712774981014206193)
              ·
                refine ⟨4492256784581235760654645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5989675712774981014206193 4492256784581235760654645)
                ·
                  refine ⟨421149073554490852561373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4492256784581235760654645 421149073554490852561373)
                  ·
                    rfl

theorem cell22_3690832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 5].length) (baseStart_3690832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690832 prefixEnd_3690832 := by exact prefixLift 3690832
  have htrace : WordTrace (prefixWord ++ tailWord_3690832) baseStart_3690832 baseEnd_3690832 := by
    simpa [prefixWord, tailWord_3690832, baseEnd_3690832] using wordTrace_append hprefix tailTrace_3690832
  have hstable : (prefixWord ++ tailWord_3690832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690832).length < 2 ^ (prefixWord ++ tailWord_3690832).sum := by decide
  have hdescent : baseEnd_3690832 < baseStart_3690832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690836 : List Nat := [2, 4, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_3690836 : Nat := 118140960795 + 3690836 * 2 ^ 59
def prefixEnd_3690836 : Nat := 4983230072969 + 3 ^ 40 * 3690836 * 2
def baseEnd_3690836 : Nat := 1263448589945217880584107

theorem tailTrace_3690836 : CollatzResearch.WordTrace tailWord_3690836 prefixEnd_3690836 1263448589945217880584107 := by
  unfold tailWord_3690836
  simp only [CollatzResearch.WordTrace]
  refine ⟨67307924028369495724806181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89743898704492660966408241 67307924028369495724806181)
  ·
    refine ⟨12620235755319280448401159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67307924028369495724806181 12620235755319280448401159)
    ·
      refine ⟨18930353632978920672601739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12620235755319280448401159 18930353632978920672601739)
      ·
        refine ⟨28395530449468381008902609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18930353632978920672601739 28395530449468381008902609)
        ·
          refine ⟨21296647837101285756676957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28395530449468381008902609 21296647837101285756676957)
          ·
            refine ⟨7986242938912982158753859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21296647837101285756676957 7986242938912982158753859)
            ·
              refine ⟨11979364408369473238130789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7986242938912982158753859 11979364408369473238130789)
              ·
                refine ⟨2246130826569276232149523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11979364408369473238130789 2246130826569276232149523)
                ·
                  refine ⟨3369196239853914348224285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2246130826569276232149523 3369196239853914348224285)
                  ·
                    refine ⟨1263448589945217880584107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3369196239853914348224285 1263448589945217880584107)
                    ·
                      rfl

theorem cell22_3690836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_3690836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690836 prefixEnd_3690836 := by exact prefixLift 3690836
  have htrace : WordTrace (prefixWord ++ tailWord_3690836) baseStart_3690836 baseEnd_3690836 := by
    simpa [prefixWord, tailWord_3690836, baseEnd_3690836] using wordTrace_append hprefix tailTrace_3690836
  have hstable : (prefixWord ++ tailWord_3690836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690836).length < 2 ^ (prefixWord ++ tailWord_3690836).sum := by decide
  have hdescent : baseEnd_3690836 < baseStart_3690836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690870 : List Nat := [5, 1, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_3690870 : Nat := 118140960795 + 3690870 * 2 ^ 59
def prefixEnd_3690870 : Nat := 4983230072969 + 3 ^ 40 * 3690870 * 2
def baseEnd_3690870 : Nat := 1263460228840053125234003

theorem tailTrace_3690870 : CollatzResearch.WordTrace tailWord_3690870 prefixEnd_3690870 1263460228840053125234003 := by
  unfold tailWord_3690870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8413568008663488453521879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 89744725425743876837566709 8413568008663488453521879)
  ·
    refine ⟨12620352012995232680282819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8413568008663488453521879 12620352012995232680282819)
    ·
      refine ⟨18930528019492849020424229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12620352012995232680282819 18930528019492849020424229)
      ·
        refine ⟨3549474003654909191329543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18930528019492849020424229 3549474003654909191329543)
        ·
          refine ⟨5324211005482363786994315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3549474003654909191329543 5324211005482363786994315)
          ·
            refine ⟨7986316508223545680491473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5324211005482363786994315 7986316508223545680491473)
            ·
              refine ⟨5989737381167659260368605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7986316508223545680491473 5989737381167659260368605)
              ·
                refine ⟨2246151517937872222638227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5989737381167659260368605 2246151517937872222638227)
                ·
                  refine ⟨3369227276906808333957341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2246151517937872222638227 3369227276906808333957341)
                  ·
                    refine ⟨1263460228840053125234003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3369227276906808333957341 1263460228840053125234003)
                    ·
                      rfl

theorem cell22_3690870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_3690870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690870 prefixEnd_3690870 := by exact prefixLift 3690870
  have htrace : WordTrace (prefixWord ++ tailWord_3690870) baseStart_3690870 baseEnd_3690870 := by
    simpa [prefixWord, tailWord_3690870, baseEnd_3690870] using wordTrace_append hprefix tailTrace_3690870
  have hstable : (prefixWord ++ tailWord_3690870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690870).length < 2 ^ (prefixWord ++ tailWord_3690870).sum := by decide
  have hdescent : baseEnd_3690870 < baseStart_3690870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690894 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 6]
def baseStart_3690894 : Nat := 118140960795 + 3690894 * 2 ^ 59
def prefixEnd_3690894 : Nat := 4983230072969 + 3 ^ 40 * 3690894 * 2
def baseEnd_3690894 : Nat := 421156148176841687544643

theorem tailTrace_3690894 : CollatzResearch.WordTrace tailWord_3690894 prefixEnd_3690894 421156148176841687544643 := by
  unfold tailWord_3690894
  simp only [CollatzResearch.WordTrace]
  refine ⟨16827245436316108419402967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89745308993685911570149157 16827245436316108419402967)
  ·
    refine ⟨25240868154474162629104451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16827245436316108419402967 25240868154474162629104451)
    ·
      refine ⟨37861302231711243943656677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25240868154474162629104451 37861302231711243943656677)
      ·
        refine ⟨7098994168445858239435627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37861302231711243943656677 7098994168445858239435627)
        ·
          refine ⟨10648491252668787359153441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7098994168445858239435627 10648491252668787359153441)
          ·
            refine ⟨7986368439501590519365081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10648491252668787359153441 7986368439501590519365081)
            ·
              refine ⟨5989776329626192889523811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7986368439501590519365081 5989776329626192889523811)
              ·
                refine ⟨8984664494439289334285717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5989776329626192889523811 8984664494439289334285717)
                ·
                  refine ⟨421156148176841687544643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8984664494439289334285717 421156148176841687544643)
                  ·
                    rfl

theorem cell22_3690894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_3690894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690894 prefixEnd_3690894 := by exact prefixLift 3690894
  have htrace : WordTrace (prefixWord ++ tailWord_3690894) baseStart_3690894 baseEnd_3690894 := by
    simpa [prefixWord, tailWord_3690894, baseEnd_3690894] using wordTrace_append hprefix tailTrace_3690894
  have hstable : (prefixWord ++ tailWord_3690894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690894).length < 2 ^ (prefixWord ++ tailWord_3690894).sum := by decide
  have hdescent : baseEnd_3690894 < baseStart_3690894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690905 : List Nat := [1, 2, 1, 2, 1, 4, 2, 9]
def baseStart_3690905 : Nat := 118140960795 + 3690905 * 2 ^ 59
def prefixEnd_3690905 : Nat := 4983230072969 + 3 ^ 40 * 3690905 * 2
def baseEnd_3690905 : Nat := 140385801117258300067655

theorem tailTrace_3690905 : CollatzResearch.WordTrace tailWord_3690905 prefixEnd_3690905 140385801117258300067655 := by
  unfold tailWord_3690905
  simp only [CollatzResearch.WordTrace]
  refine ⟨134618364693489016233874169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89745576462326010822582779 134618364693489016233874169)
  ·
    refine ⟨100963773520116762175405627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134618364693489016233874169 100963773520116762175405627)
    ·
      refine ⟨151445660280175143263108441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100963773520116762175405627 151445660280175143263108441)
      ·
        refine ⟨113584245210131357447331331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151445660280175143263108441 113584245210131357447331331)
        ·
          refine ⟨170376367815197036170996997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113584245210131357447331331 170376367815197036170996997)
          ·
            refine ⟨31945568965349444282061937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170376367815197036170996997 31945568965349444282061937)
            ·
              refine ⟨23959176724012083211546453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31945568965349444282061937 23959176724012083211546453)
              ·
                refine ⟨140385801117258300067655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23959176724012083211546453 140385801117258300067655)
                ·
                  rfl

theorem cell22_3690905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 9].length) (baseStart_3690905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690905 prefixEnd_3690905 := by exact prefixLift 3690905
  have htrace : WordTrace (prefixWord ++ tailWord_3690905) baseStart_3690905 baseEnd_3690905 := by
    simpa [prefixWord, tailWord_3690905, baseEnd_3690905] using wordTrace_append hprefix tailTrace_3690905
  have hstable : (prefixWord ++ tailWord_3690905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690905).length < 2 ^ (prefixWord ++ tailWord_3690905).sum := by decide
  have hdescent : baseEnd_3690905 < baseStart_3690905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3690945 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 6]
def baseStart_3690945 : Nat := 118140960795 + 3690945 * 2 ^ 59
def prefixEnd_3690945 : Nat := 4983230072969 + 3 ^ 40 * 3690945 * 2
def baseEnd_3690945 : Nat := 421161967624259309869591

theorem tailTrace_3690945 : CollatzResearch.WordTrace tailWord_3690945 prefixEnd_3690945 421161967624259309869591 := by
  unfold tailWord_3690945
  simp only [CollatzResearch.WordTrace]
  refine ⟨134619823613344103065330289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89746549075562735376886859 134619823613344103065330289)
  ·
    refine ⟨100964867710008077298997717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134619823613344103065330289 100964867710008077298997717)
    ·
      refine ⟨2366364086953314311695259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 100964867710008077298997717 2366364086953314311695259)
      ·
        refine ⟨3549546130429971467542889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2366364086953314311695259 3549546130429971467542889)
        ·
          refine ⟨2662159597822478600657167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3549546130429971467542889 2662159597822478600657167)
          ·
            refine ⟨3993239396733717900985751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662159597822478600657167 3993239396733717900985751)
            ·
              refine ⟨5989859095100576851478627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3993239396733717900985751 5989859095100576851478627)
              ·
                refine ⟨8984788642650865277217941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5989859095100576851478627 8984788642650865277217941)
                ·
                  refine ⟨421161967624259309869591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8984788642650865277217941 421161967624259309869591)
                  ·
                    rfl

theorem cell22_3690945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 6].length) (baseStart_3690945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3690945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3690945 prefixEnd_3690945 := by exact prefixLift 3690945
  have htrace : WordTrace (prefixWord ++ tailWord_3690945) baseStart_3690945 baseEnd_3690945 := by
    simpa [prefixWord, tailWord_3690945, baseEnd_3690945] using wordTrace_append hprefix tailTrace_3690945
  have hstable : (prefixWord ++ tailWord_3690945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3690945).length < 2 ^ (prefixWord ++ tailWord_3690945).sum := by decide
  have hdescent : baseEnd_3690945 < baseStart_3690945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3690945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691048 : List Nat := [2, 1, 5, 2, 1, 1, 4, 1, 1, 4]
def baseStart_3691048 : Nat := 118140960795 + 3691048 * 2 ^ 59
def prefixEnd_3691048 : Nat := 4983230072969 + 3 ^ 40 * 3691048 * 2
def baseEnd_3691048 : Nat := 1263521161877719994283457

theorem tailTrace_3691048 : CollatzResearch.WordTrace tailWord_3691048 prefixEnd_3691048 1263521161877719994283457 := by
  unfold tailWord_3691048
  simp only [CollatzResearch.WordTrace]
  refine ⟨67311790165985475828164899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89749053554647301104219865 67311790165985475828164899)
  ·
    refine ⟨100967685248978213742247349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67311790165985475828164899 100967685248978213742247349)
    ·
      refine ⟨9465720492091707538335689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100967685248978213742247349 9465720492091707538335689)
      ·
        refine ⟨7099290369068780653751767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9465720492091707538335689 7099290369068780653751767)
        ·
          refine ⟨10648935553603170980627651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7099290369068780653751767 10648935553603170980627651)
          ·
            refine ⟨15973403330404756470941477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10648935553603170980627651 15973403330404756470941477)
            ·
              refine ⟨2995013124450891838301527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15973403330404756470941477 2995013124450891838301527)
              ·
                refine ⟨4492519686676337757452291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2995013124450891838301527 4492519686676337757452291)
                ·
                  refine ⟨6738779530014506636178437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4492519686676337757452291 6738779530014506636178437)
                  ·
                    refine ⟨1263521161877719994283457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6738779530014506636178437 1263521161877719994283457)
                    ·
                      rfl

theorem cell22_3691048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_3691048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691048 prefixEnd_3691048 := by exact prefixLift 3691048
  have htrace : WordTrace (prefixWord ++ tailWord_3691048) baseStart_3691048 baseEnd_3691048 := by
    simpa [prefixWord, tailWord_3691048, baseEnd_3691048] using wordTrace_append hprefix tailTrace_3691048
  have hstable : (prefixWord ++ tailWord_3691048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691048).length < 2 ^ (prefixWord ++ tailWord_3691048).sum := by decide
  have hdescent : baseEnd_3691048 < baseStart_3691048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691078 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_3691078 : Nat := 118140960795 + 3691078 * 2 ^ 59
def prefixEnd_3691078 : Nat := 4983230072969 + 3 ^ 40 * 3691078 * 2
def baseEnd_3691078 : Nat := 1263531431490809916033365

theorem tailTrace_3691078 : CollatzResearch.WordTrace tailWord_3691078 prefixEnd_3691078 1263531431490809916033365 := by
  unfold tailWord_3691078
  simp only [CollatzResearch.WordTrace]
  refine ⟨4207021078808195836872559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 89749783014574844519947925 4207021078808195836872559)
  ·
    refine ⟨6310531618212293755308839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4207021078808195836872559 6310531618212293755308839)
    ·
      refine ⟨9465797427318440632963259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6310531618212293755308839 9465797427318440632963259)
      ·
        refine ⟨14198696140977660949444889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9465797427318440632963259 14198696140977660949444889)
        ·
          refine ⟨10649022105733245712083667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14198696140977660949444889 10649022105733245712083667)
          ·
            refine ⟨15973533158599868568125501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10649022105733245712083667 15973533158599868568125501)
            ·
              refine ⟨5990074934474950713047063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15973533158599868568125501 5990074934474950713047063)
              ·
                refine ⟨8985112401712426069570595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5990074934474950713047063 8985112401712426069570595)
                ·
                  refine ⟨13477668602568639104355893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8985112401712426069570595 13477668602568639104355893)
                  ·
                    refine ⟨1263531431490809916033365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13477668602568639104355893 1263531431490809916033365)
                    ·
                      rfl

theorem cell22_3691078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_3691078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691078 prefixEnd_3691078 := by exact prefixLift 3691078
  have htrace : WordTrace (prefixWord ++ tailWord_3691078) baseStart_3691078 baseEnd_3691078 := by
    simpa [prefixWord, tailWord_3691078, baseEnd_3691078] using wordTrace_append hprefix tailTrace_3691078
  have hstable : (prefixWord ++ tailWord_3691078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691078).length < 2 ^ (prefixWord ++ tailWord_3691078).sum := by decide
  have hdescent : baseEnd_3691078 < baseStart_3691078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691087 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 2, 6]
def baseStart_3691087 : Nat := 118140960795 + 3691087 * 2 ^ 59
def prefixEnd_3691087 : Nat := 4983230072969 + 3 ^ 40 * 3691087 * 2
def baseEnd_3691087 : Nat := 1263534512374736892558337

theorem tailTrace_3691087 : CollatzResearch.WordTrace tailWord_3691087 prefixEnd_3691087 1263534512374736892558337 := by
  unfold tailWord_3691087
  simp only [CollatzResearch.WordTrace]
  refine ⟨134625002778829661316999515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89750001852553107544666343 134625002778829661316999515)
  ·
    refine ⟨201937504168244491975499273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134625002778829661316999515 201937504168244491975499273)
    ·
      refine ⟨151453128126183368981624455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201937504168244491975499273 151453128126183368981624455)
      ·
        refine ⟨227179692189275053472436683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151453128126183368981624455 227179692189275053472436683)
        ·
          refine ⟨340769538283912580208655025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227179692189275053472436683 340769538283912580208655025)
          ·
            refine ⟨255577153712934435156491269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340769538283912580208655025 255577153712934435156491269)
            ·
              refine ⟨47920716321175206591842113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 255577153712934435156491269 47920716321175206591842113)
              ·
                refine ⟨35940537240881404943881585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47920716321175206591842113 35940537240881404943881585)
                ·
                  refine ⟨26955402930661053707911189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35940537240881404943881585 26955402930661053707911189)
                  ·
                    refine ⟨1263534512374736892558337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26955402930661053707911189 1263534512374736892558337)
                    ·
                      rfl

theorem cell22_3691087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 6].length) (baseStart_3691087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691087 prefixEnd_3691087 := by exact prefixLift 3691087
  have htrace : WordTrace (prefixWord ++ tailWord_3691087) baseStart_3691087 baseEnd_3691087 := by
    simpa [prefixWord, tailWord_3691087, baseEnd_3691087] using wordTrace_append hprefix tailTrace_3691087
  have hstable : (prefixWord ++ tailWord_3691087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691087).length < 2 ^ (prefixWord ++ tailWord_3691087).sum := by decide
  have hdescent : baseEnd_3691087 < baseStart_3691087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691136 : List Nat := [2, 1, 1, 2, 1, 5, 4, 1, 5]
def baseStart_3691136 : Nat := 118140960795 + 3691136 * 2 ^ 59
def prefixEnd_3691136 : Nat := 4983230072969 + 3 ^ 40 * 3691136 * 2
def baseEnd_3691136 : Nat := 421183762025372366027729

theorem tailTrace_3691136 : CollatzResearch.WordTrace tailWord_3691136 prefixEnd_3691136 421183762025372366027729 := by
  unfold tailWord_3691136
  simp only [CollatzResearch.WordTrace]
  refine ⟨67313394977826071342766631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89751193303768095123688841 67313394977826071342766631)
  ·
    refine ⟨100970092466739107014149947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67313394977826071342766631 100970092466739107014149947)
    ·
      refine ⟨151455138700108660521224921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100970092466739107014149947 151455138700108660521224921)
      ·
        refine ⟨113591354025081495390918691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151455138700108660521224921 113591354025081495390918691)
        ·
          refine ⟨170387031037622243086378037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113591354025081495390918691 170387031037622243086378037)
          ·
            refine ⟨15973784159777085289347941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170387031037622243086378037 15973784159777085289347941)
            ·
              refine ⟨2995084529958203491752739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15973784159777085289347941 2995084529958203491752739)
              ·
                refine ⟨4492626794937305237629109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2995084529958203491752739 4492626794937305237629109)
                ·
                  refine ⟨421183762025372366027729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4492626794937305237629109 421183762025372366027729)
                  ·
                    rfl

theorem cell22_3691136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 5].length) (baseStart_3691136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691136 prefixEnd_3691136 := by exact prefixLift 3691136
  have htrace : WordTrace (prefixWord ++ tailWord_3691136) baseStart_3691136 baseEnd_3691136 := by
    simpa [prefixWord, tailWord_3691136, baseEnd_3691136] using wordTrace_append hprefix tailTrace_3691136
  have hstable : (prefixWord ++ tailWord_3691136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691136).length < 2 ^ (prefixWord ++ tailWord_3691136).sum := by decide
  have hdescent : baseEnd_3691136 < baseStart_3691136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691194 : List Nat := [3, 1, 1, 1, 2, 3, 2, 2, 1, 6]
def baseStart_3691194 : Nat := 118140960795 + 3691194 * 2 ^ 59
def prefixEnd_3691194 : Nat := 4983230072969 + 3 ^ 40 * 3691194 * 2
def baseEnd_3691194 : Nat := 1263571140661424280133009

theorem tailTrace_3691194 : CollatzResearch.WordTrace tailWord_3691194 prefixEnd_3691194 1263571140661424280133009 := by
  unfold tailWord_3691194
  simp only [CollatzResearch.WordTrace]
  refine ⟨33657226347360504647786159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89752603592961345727429757 33657226347360504647786159)
  ·
    refine ⟨50485839521040756971679239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33657226347360504647786159 50485839521040756971679239)
    ·
      refine ⟨75728759281561135457518859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50485839521040756971679239 75728759281561135457518859)
      ·
        refine ⟨113593138922341703186278289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75728759281561135457518859 113593138922341703186278289)
        ·
          refine ⟨85194854191756277389708717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113593138922341703186278289 85194854191756277389708717)
          ·
            refine ⟨31948070321908604021140769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85194854191756277389708717 31948070321908604021140769)
            ·
              refine ⟨23961052741431453015855577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31948070321908604021140769 23961052741431453015855577)
              ·
                refine ⟨17970789556073589761891683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23961052741431453015855577 17970789556073589761891683)
                ·
                  refine ⟨26956184334110384642837525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17970789556073589761891683 26956184334110384642837525)
                  ·
                    refine ⟨1263571140661424280133009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26956184334110384642837525 1263571140661424280133009)
                    ·
                      rfl

theorem cell22_3691194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_3691194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691194 prefixEnd_3691194 := by exact prefixLift 3691194
  have htrace : WordTrace (prefixWord ++ tailWord_3691194) baseStart_3691194 baseEnd_3691194 := by
    simpa [prefixWord, tailWord_3691194, baseEnd_3691194] using wordTrace_append hprefix tailTrace_3691194
  have hstable : (prefixWord ++ tailWord_3691194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691194).length < 2 ^ (prefixWord ++ tailWord_3691194).sum := by decide
  have hdescent : baseEnd_3691194 < baseStart_3691194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691196 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 1, 5]
def baseStart_3691196 : Nat := 118140960795 + 3691196 * 2 ^ 59
def prefixEnd_3691196 : Nat := 4983230072969 + 3 ^ 40 * 3691196 * 2
def baseEnd_3691196 : Nat := 1263571825302296941583003

theorem tailTrace_3691196 : CollatzResearch.WordTrace tailWord_3691196 prefixEnd_3691196 1263571825302296941583003 := by
  unfold tailWord_3691196
  simp only [CollatzResearch.WordTrace]
  refine ⟨67314489167717386466358721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89752652223623181955144961 67314489167717386466358721)
  ·
    refine ⟨50485866875788039849769041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67314489167717386466358721 50485866875788039849769041)
    ·
      refine ⟨37864400156841029887326781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50485866875788039849769041 37864400156841029887326781)
      ·
        refine ⟨14199150058815386207747543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37864400156841029887326781 14199150058815386207747543)
        ·
          refine ⟨21298725088223079311621315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14199150058815386207747543 21298725088223079311621315)
          ·
            refine ⟨31948087632334618967431973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21298725088223079311621315 31948087632334618967431973)
            ·
              refine ⟨5990266431062741056393495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31948087632334618967431973 5990266431062741056393495)
              ·
                refine ⟨8985399646594111584590243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5990266431062741056393495 8985399646594111584590243)
                ·
                  refine ⟨13478099469891167376885365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8985399646594111584590243 13478099469891167376885365)
                  ·
                    refine ⟨1263571825302296941583003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13478099469891167376885365 1263571825302296941583003)
                    ·
                      rfl

theorem cell22_3691196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_3691196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691196 prefixEnd_3691196 := by exact prefixLift 3691196
  have htrace : WordTrace (prefixWord ++ tailWord_3691196) baseStart_3691196 baseEnd_3691196 := by
    simpa [prefixWord, tailWord_3691196, baseEnd_3691196] using wordTrace_append hprefix tailTrace_3691196
  have hstable : (prefixWord ++ tailWord_3691196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691196).length < 2 ^ (prefixWord ++ tailWord_3691196).sum := by decide
  have hdescent : baseEnd_3691196 < baseStart_3691196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691241 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 3, 3]
def baseStart_3691241 : Nat := 118140960795 + 3691241 * 2 ^ 59
def prefixEnd_3691241 : Nat := 4983230072969 + 3 ^ 40 * 3691241 * 2
def baseEnd_3691241 : Nat := 1263587229721931824207865

theorem tailTrace_3691241 : CollatzResearch.WordTrace tailWord_3691241 prefixEnd_3691241 1263587229721931824207865 := by
  unfold tailWord_3691241
  simp only [CollatzResearch.WordTrace]
  refine ⟨134630619620271745618105577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89753746413514497078737051 134630619620271745618105577)
  ·
    refine ⟨100972964715203809213579183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134630619620271745618105577 100972964715203809213579183)
    ·
      refine ⟨151459447072805713820368775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100972964715203809213579183 151459447072805713820368775)
      ·
        refine ⟨227189170609208570730553163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151459447072805713820368775 227189170609208570730553163)
        ·
          refine ⟨340783755913812856095829745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 227189170609208570730553163 340783755913812856095829745)
          ·
            refine ⟨255587816935359642071872309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 340783755913812856095829745 255587816935359642071872309)
            ·
              refine ⟨23961357837689966444238029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 255587816935359642071872309 23961357837689966444238029)
              ·
                refine ⟨8985509189133737416589261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23961357837689966444238029 8985509189133737416589261)
                ·
                  refine ⟨3369565945925151531220973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8985509189133737416589261 3369565945925151531220973)
                  ·
                    refine ⟨1263587229721931824207865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3369565945925151531220973 1263587229721931824207865)
                    ·
                      rfl

theorem cell22_3691241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3, 3].length) (baseStart_3691241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691241 prefixEnd_3691241 := by exact prefixLift 3691241
  have htrace : WordTrace (prefixWord ++ tailWord_3691241) baseStart_3691241 baseEnd_3691241 := by
    simpa [prefixWord, tailWord_3691241, baseEnd_3691241] using wordTrace_append hprefix tailTrace_3691241
  have hstable : (prefixWord ++ tailWord_3691241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691241).length < 2 ^ (prefixWord ++ tailWord_3691241).sum := by decide
  have hdescent : baseEnd_3691241 < baseStart_3691241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691269 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 1, 7]
def baseStart_3691269 : Nat := 118140960795 + 3691269 * 2 ^ 59
def prefixEnd_3691269 : Nat := 4983230072969 + 3 ^ 40 * 3691269 * 2
def baseEnd_3691269 : Nat := 1263596814694149084507779

theorem tailTrace_3691269 : CollatzResearch.WordTrace tailWord_3691269 prefixEnd_3691269 1263596814694149084507779 := by
  unfold tailWord_3691269
  simp only [CollatzResearch.WordTrace]
  refine ⟨134631640864170306400124861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89754427242780204266749907 134631640864170306400124861)
  ·
    refine ⟨50486865324063864900046823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134631640864170306400124861 50486865324063864900046823)
    ·
      refine ⟨75730297986095797350070235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50486865324063864900046823 75730297986095797350070235)
      ·
        refine ⟨113595446979143696025105353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75730297986095797350070235 113595446979143696025105353)
        ·
          refine ⟨85196585234357772018829015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113595446979143696025105353 85196585234357772018829015)
          ·
            refine ⟨127794877851536658028243523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85196585234357772018829015 127794877851536658028243523)
            ·
              refine ⟨191692316777304987042365285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127794877851536658028243523 191692316777304987042365285)
              ·
                refine ⟨35942309395744685070443491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 191692316777304987042365285 35942309395744685070443491)
                ·
                  refine ⟨53913464093617027605665237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35942309395744685070443491 53913464093617027605665237)
                  ·
                    refine ⟨1263596814694149084507779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53913464093617027605665237 1263596814694149084507779)
                    ·
                      rfl

theorem cell22_3691269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_3691269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691269 prefixEnd_3691269 := by exact prefixLift 3691269
  have htrace : WordTrace (prefixWord ++ tailWord_3691269) baseStart_3691269 baseEnd_3691269 := by
    simpa [prefixWord, tailWord_3691269, baseEnd_3691269] using wordTrace_append hprefix tailTrace_3691269
  have hstable : (prefixWord ++ tailWord_3691269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691269).length < 2 ^ (prefixWord ++ tailWord_3691269).sum := by decide
  have hdescent : baseEnd_3691269 < baseStart_3691269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691271 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 7]
def baseStart_3691271 : Nat := 118140960795 + 3691271 * 2 ^ 59
def prefixEnd_3691271 : Nat := 4983230072969 + 3 ^ 40 * 3691271 * 2
def baseEnd_3691271 : Nat := 421199166445007248652591

theorem tailTrace_3691271 : CollatzResearch.WordTrace tailWord_3691271 prefixEnd_3691271 421199166445007248652591 := by
  unfold tailWord_3691271
  simp only [CollatzResearch.WordTrace]
  refine ⟨134631713810163060741697667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89754475873442040494465111 134631713810163060741697667)
  ·
    refine ⟨201947570715244591112546501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134631713810163060741697667 201947570715244591112546501)
    ·
      refine ⟨37865169509108360833602469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 201947570715244591112546501 37865169509108360833602469)
      ·
        refine ⟨7099719282957817656300463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37865169509108360833602469 7099719282957817656300463)
        ·
          refine ⟨10649578924436726484450695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7099719282957817656300463 10649578924436726484450695)
          ·
            refine ⟨15974368386655089726676043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10649578924436726484450695 15974368386655089726676043)
            ·
              refine ⟨23961552579982634590014065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15974368386655089726676043 23961552579982634590014065)
              ·
                refine ⟨17971164434986975942510549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23961552579982634590014065 17971164434986975942510549)
                ·
                  refine ⟨421199166445007248652591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17971164434986975942510549 421199166445007248652591)
                  ·
                    rfl

theorem cell22_3691271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 7].length) (baseStart_3691271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691271 prefixEnd_3691271 := by exact prefixLift 3691271
  have htrace : WordTrace (prefixWord ++ tailWord_3691271) baseStart_3691271 baseEnd_3691271 := by
    simpa [prefixWord, tailWord_3691271, baseEnd_3691271] using wordTrace_append hprefix tailTrace_3691271
  have hstable : (prefixWord ++ tailWord_3691271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691271).length < 2 ^ (prefixWord ++ tailWord_3691271).sum := by decide
  have hdescent : baseEnd_3691271 < baseStart_3691271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691292 : List Nat := [2, 2, 3, 1, 1, 4, 3, 2, 1, 3]
def baseStart_3691292 : Nat := 118140960795 + 3691292 * 2 ^ 59
def prefixEnd_3691292 : Nat := 4983230072969 + 3 ^ 40 * 3691292 * 2
def baseEnd_3691292 : Nat := 1263604688064184691182709

theorem tailTrace_3691292 : CollatzResearch.WordTrace tailWord_3691292 prefixEnd_3691292 1263604688064184691182709 := by
  unfold tailWord_3691292
  simp only [CollatzResearch.WordTrace]
  refine ⟨67316239871543490664106065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89754986495391320885474753 67316239871543490664106065)
  ·
    refine ⟨50487179903657617998079549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67316239871543490664106065 50487179903657617998079549)
    ·
      refine ⟨18932692463871606749279831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50487179903657617998079549 18932692463871606749279831)
      ·
        refine ⟨28399038695807410123919747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18932692463871606749279831 28399038695807410123919747)
        ·
          refine ⟨42598558043711115185879621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28399038695807410123919747 42598558043711115185879621)
          ·
            refine ⟨7987229633195834097352429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42598558043711115185879621 7987229633195834097352429)
            ·
              refine ⟨2995211112448437786507161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7987229633195834097352429 2995211112448437786507161)
              ·
                refine ⟨2246408334336328339880371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2995211112448437786507161 2246408334336328339880371)
                ·
                  refine ⟨3369612501504492509820557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2246408334336328339880371 3369612501504492509820557)
                  ·
                    refine ⟨1263604688064184691182709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3369612501504492509820557 1263604688064184691182709)
                    ·
                      rfl

theorem cell22_3691292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_3691292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691292 prefixEnd_3691292 := by exact prefixLift 3691292
  have htrace : WordTrace (prefixWord ++ tailWord_3691292) baseStart_3691292 baseEnd_3691292 := by
    simpa [prefixWord, tailWord_3691292, baseEnd_3691292] using wordTrace_append hprefix tailTrace_3691292
  have hstable : (prefixWord ++ tailWord_3691292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691292).length < 2 ^ (prefixWord ++ tailWord_3691292).sum := by decide
  have hdescent : baseEnd_3691292 < baseStart_3691292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691301 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 3, 4]
def baseStart_3691301 : Nat := 118140960795 + 3691301 * 2 ^ 59
def prefixEnd_3691301 : Nat := 4983230072969 + 3 ^ 40 * 3691301 * 2
def baseEnd_3691301 : Nat := 1263607768948111667707681

theorem tailTrace_3691301 : CollatzResearch.WordTrace tailWord_3691301 prefixEnd_3691301 1263607768948111667707681 := by
  unfold tailWord_3691301
  simp only [CollatzResearch.WordTrace]
  refine ⟨134632808000054375865289757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89755205333369583910193171 134632808000054375865289757)
  ·
    refine ⟨50487303000020390949483659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 134632808000054375865289757 50487303000020390949483659)
    ·
      refine ⟨75730954500030586424225489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50487303000020390949483659 75730954500030586424225489)
      ·
        refine ⟨56798215875022939818169117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75730954500030586424225489 56798215875022939818169117)
        ·
          refine ⟨21299330953133602431813419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56798215875022939818169117 21299330953133602431813419)
          ·
            refine ⟨31948996429700403647720129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21299330953133602431813419 31948996429700403647720129)
            ·
              refine ⟨23961747322275302735790097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31948996429700403647720129 23961747322275302735790097)
              ·
                refine ⟨17971310491706477051842573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23961747322275302735790097 17971310491706477051842573)
                ·
                  refine ⟨6739241434389928894440965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17971310491706477051842573 6739241434389928894440965)
                  ·
                    refine ⟨1263607768948111667707681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6739241434389928894440965 1263607768948111667707681)
                    ·
                      rfl

theorem cell22_3691301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_3691301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691301 prefixEnd_3691301 := by exact prefixLift 3691301
  have htrace : WordTrace (prefixWord ++ tailWord_3691301) baseStart_3691301 baseEnd_3691301 := by
    simpa [prefixWord, tailWord_3691301, baseEnd_3691301] using wordTrace_append hprefix tailTrace_3691301
  have hstable : (prefixWord ++ tailWord_3691301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691301).length < 2 ^ (prefixWord ++ tailWord_3691301).sum := by decide
  have hdescent : baseEnd_3691301 < baseStart_3691301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691331 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 1, 5]
def baseStart_3691331 : Nat := 118140960795 + 3691331 * 2 ^ 59
def prefixEnd_3691331 : Nat := 4983230072969 + 3 ^ 40 * 3691331 * 2
def baseEnd_3691331 : Nat := 1263618038561201589457589

theorem tailTrace_3691331 : CollatzResearch.WordTrace tailWord_3691331 prefixEnd_3691331 1263618038561201589457589 := by
  unfold tailWord_3691331
  simp only [CollatzResearch.WordTrace]
  refine ⟨134633902189945690988881847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89755934793297127325921231 134633902189945690988881847)
  ·
    refine ⟨201950853284918536483322771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134633902189945690988881847 201950853284918536483322771)
    ·
      refine ⟨302926279927377804724984157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201950853284918536483322771 302926279927377804724984157)
      ·
        refine ⟨113597354972766676771869059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 302926279927377804724984157 113597354972766676771869059)
        ·
          refine ⟨170396032459150015157803589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113597354972766676771869059 170396032459150015157803589)
          ·
            refine ⟨31949256086090627842088173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 170396032459150015157803589 31949256086090627842088173)
            ·
              refine ⟨11980971032283985440783065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31949256086090627842088173 11980971032283985440783065)
              ·
                refine ⟨8985728274212989080587299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11980971032283985440783065 8985728274212989080587299)
                ·
                  refine ⟨13478592411319483620880949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8985728274212989080587299 13478592411319483620880949)
                  ·
                    refine ⟨1263618038561201589457589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13478592411319483620880949 1263618038561201589457589)
                    ·
                      rfl

theorem cell22_3691331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 1, 5].length) (baseStart_3691331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691331 prefixEnd_3691331 := by exact prefixLift 3691331
  have htrace : WordTrace (prefixWord ++ tailWord_3691331) baseStart_3691331 baseEnd_3691331 := by
    simpa [prefixWord, tailWord_3691331, baseEnd_3691331] using wordTrace_append hprefix tailTrace_3691331
  have hstable : (prefixWord ++ tailWord_3691331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691331).length < 2 ^ (prefixWord ++ tailWord_3691331).sum := by decide
  have hdescent : baseEnd_3691331 < baseStart_3691331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691487 : List Nat := [1, 1, 2, 3, 5, 2, 1, 2, 1, 4]
def baseStart_3691487 : Nat := 118140960795 + 3691487 * 2 ^ 59
def prefixEnd_3691487 : Nat := 4983230072969 + 3 ^ 40 * 3691487 * 2
def baseEnd_3691487 : Nat := 1263671440549269182557111

theorem tailTrace_3691487 : CollatzResearch.WordTrace tailWord_3691487 prefixEnd_3691487 1263671440549269182557111 := by
  unfold tailWord_3691487
  simp only [CollatzResearch.WordTrace]
  refine ⟨134639591977380529631560715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89759727984920353087707143 134639591977380529631560715)
  ·
    refine ⟨201959387966070794447341073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134639591977380529631560715 201959387966070794447341073)
    ·
      refine ⟨151469540974553095835505805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 201959387966070794447341073 151469540974553095835505805)
      ·
        refine ⟨56801077865457410938314677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 151469540974553095835505805 56801077865457410938314677)
        ·
          refine ⟨5325101049886632275467001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56801077865457410938314677 5325101049886632275467001)
          ·
            refine ⟨3993825787414974206600251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5325101049886632275467001 3993825787414974206600251)
            ·
              refine ⟨5990738681122461309900377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3993825787414974206600251 5990738681122461309900377)
              ·
                refine ⟨4493054010841845982425283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5990738681122461309900377 4493054010841845982425283)
                ·
                  refine ⟨6739581016262768973637925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493054010841845982425283 6739581016262768973637925)
                  ·
                    refine ⟨1263671440549269182557111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6739581016262768973637925 1263671440549269182557111)
                    ·
                      rfl

theorem cell22_3691487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 1, 4].length) (baseStart_3691487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691487 prefixEnd_3691487 := by exact prefixLift 3691487
  have htrace : WordTrace (prefixWord ++ tailWord_3691487) baseStart_3691487 baseEnd_3691487 := by
    simpa [prefixWord, tailWord_3691487, baseEnd_3691487] using wordTrace_append hprefix tailTrace_3691487
  have hstable : (prefixWord ++ tailWord_3691487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691487).length < 2 ^ (prefixWord ++ tailWord_3691487).sum := by decide
  have hdescent : baseEnd_3691487 < baseStart_3691487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691530 : List Nat := [3, 1, 2, 2, 3, 3, 1, 7]
def baseStart_3691530 : Nat := 118140960795 + 3691530 * 2 ^ 59
def prefixEnd_3691530 : Nat := 4983230072969 + 3 ^ 40 * 3691530 * 2
def baseEnd_3691530 : Nat := 140409573369781267081331

theorem tailTrace_3691530 : CollatzResearch.WordTrace tailWord_3691530 prefixEnd_3691530 140409573369781267081331 := by
  unfold tailWord_3691530
  simp only [CollatzResearch.WordTrace]
  refine ⟨33660290079056186993844011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89760773544149831983584029 33660290079056186993844011)
  ·
    refine ⟨50490435118584280490766017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33660290079056186993844011 50490435118584280490766017)
    ·
      refine ⟨37867826338938210368074513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50490435118584280490766017 37867826338938210368074513)
      ·
        refine ⟨28400869754203657776055885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37867826338938210368074513 28400869754203657776055885)
        ·
          refine ⟨10650326157826371666020957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28400869754203657776055885 10650326157826371666020957)
          ·
            refine ⟨3993872309184889374757859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10650326157826371666020957 3993872309184889374757859)
            ·
              refine ⟨5990808463777334062136789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3993872309184889374757859 5990808463777334062136789)
              ·
                refine ⟨140409573369781267081331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5990808463777334062136789 140409573369781267081331)
                ·
                  rfl

theorem cell22_3691530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 7].length) (baseStart_3691530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691530 prefixEnd_3691530 := by exact prefixLift 3691530
  have htrace : WordTrace (prefixWord ++ tailWord_3691530) baseStart_3691530 baseEnd_3691530 := by
    simpa [prefixWord, tailWord_3691530, baseEnd_3691530] using wordTrace_append hprefix tailTrace_3691530
  have hstable : (prefixWord ++ tailWord_3691530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691530).length < 2 ^ (prefixWord ++ tailWord_3691530).sum := by decide
  have hdescent : baseEnd_3691530 < baseStart_3691530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691549 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 2, 4]
def baseStart_3691549 : Nat := 118140960795 + 3691549 * 2 ^ 59
def prefixEnd_3691549 : Nat := 4983230072969 + 3 ^ 40 * 3691549 * 2
def baseEnd_3691549 : Nat := 1263692664416321687506921

theorem tailTrace_3691549 : CollatzResearch.WordTrace tailWord_3691549 prefixEnd_3691549 1263692664416321687506921 := by
  unfold tailWord_3691549
  simp only [CollatzResearch.WordTrace]
  refine ⟨134641853303155914220317701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89761235535437276146878467 134641853303155914220317701)
  ·
    refine ⟨25245347494341733916309569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134641853303155914220317701 25245347494341733916309569)
    ·
      refine ⟨18934010620756300437232177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25245347494341733916309569 18934010620756300437232177)
      ·
        refine ⟨14200507965567225327924133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18934010620756300437232177 14200507965567225327924133)
        ·
          refine ⟨2662595243543854748985775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14200507965567225327924133 2662595243543854748985775)
          ·
            refine ⟨3993892865315782123478663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662595243543854748985775 3993892865315782123478663)
            ·
              refine ⟨5990839297973673185217995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3993892865315782123478663 5990839297973673185217995)
              ·
                refine ⟨8986258946960509777826993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5990839297973673185217995 8986258946960509777826993)
                ·
                  refine ⟨6739694210220382333370245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8986258946960509777826993 6739694210220382333370245)
                  ·
                    refine ⟨1263692664416321687506921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6739694210220382333370245 1263692664416321687506921)
                    ·
                      rfl

theorem cell22_3691549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_3691549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691549 prefixEnd_3691549 := by exact prefixLift 3691549
  have htrace : WordTrace (prefixWord ++ tailWord_3691549) baseStart_3691549 baseEnd_3691549 := by
    simpa [prefixWord, tailWord_3691549, baseEnd_3691549] using wordTrace_append hprefix tailTrace_3691549
  have hstable : (prefixWord ++ tailWord_3691549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691549).length < 2 ^ (prefixWord ++ tailWord_3691549).sum := by decide
  have hdescent : baseEnd_3691549 < baseStart_3691549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691613 : List Nat := [1, 4, 4, 1, 2, 2, 1, 3, 1, 3]
def baseStart_3691613 : Nat := 118140960795 + 3691613 * 2 ^ 59
def prefixEnd_3691613 : Nat := 4983230072969 + 3 ^ 40 * 3691613 * 2
def baseEnd_3691613 : Nat := 1263714572924246853906725

theorem tailTrace_3691613 : CollatzResearch.WordTrace tailWord_3691613 prefixEnd_3691613 1263714572924246853906725 := by
  unfold tailWord_3691613
  simp only [CollatzResearch.WordTrace]
  refine ⟨134644187574924053150647493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89762791716616035433764995 134644187574924053150647493)
  ·
    refine ⟨25245785170298259965746405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 134644187574924053150647493 25245785170298259965746405)
    ·
      refine ⟨4733584719430923743577451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25245785170298259965746405 4733584719430923743577451)
      ·
        refine ⟨7100377079146385615366177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4733584719430923743577451 7100377079146385615366177)
        ·
          refine ⟨5325282809359789211524633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7100377079146385615366177 5325282809359789211524633)
          ·
            refine ⟨3993962107019841908643475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5325282809359789211524633 3993962107019841908643475)
            ·
              refine ⟨5990943160529762862965213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3993962107019841908643475 5990943160529762862965213)
              ·
                refine ⟨2246603685198661073611955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5990943160529762862965213 2246603685198661073611955)
                ·
                  refine ⟨3369905527797991610417933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2246603685198661073611955 3369905527797991610417933)
                  ·
                    refine ⟨1263714572924246853906725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3369905527797991610417933 1263714572924246853906725)
                    ·
                      rfl

theorem cell22_3691613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_3691613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691613 prefixEnd_3691613 := by exact prefixLift 3691613
  have htrace : WordTrace (prefixWord ++ tailWord_3691613) baseStart_3691613 baseEnd_3691613 := by
    simpa [prefixWord, tailWord_3691613, baseEnd_3691613] using wordTrace_append hprefix tailTrace_3691613
  have hstable : (prefixWord ++ tailWord_3691613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691613).length < 2 ^ (prefixWord ++ tailWord_3691613).sum := by decide
  have hdescent : baseEnd_3691613 < baseStart_3691613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691633 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 3, 6]
def baseStart_3691633 : Nat := 118140960795 + 3691633 * 2 ^ 59
def prefixEnd_3691633 : Nat := 4983230072969 + 3 ^ 40 * 3691633 * 2
def baseEnd_3691633 : Nat := 1263721419332973468406663

theorem tailTrace_3691633 : CollatzResearch.WordTrace tailWord_3691633 prefixEnd_3691633 1263721419332973468406663 := by
  unfold tailWord_3691633
  simp only [CollatzResearch.WordTrace]
  refine ⟨134644917034851596566375553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89763278023234397710917035 134644917034851596566375553)
  ·
    refine ⟨100983687776138697424781665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134644917034851596566375553 100983687776138697424781665)
    ·
      refine ⟨75737765832104023068586249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100983687776138697424781665 75737765832104023068586249)
      ·
        refine ⟨56803324374078017301439687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75737765832104023068586249 56803324374078017301439687)
        ·
          refine ⟨85204986561117025952159531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56803324374078017301439687 85204986561117025952159531)
          ·
            refine ⟨127807479841675538928239297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85204986561117025952159531 127807479841675538928239297)
            ·
              refine ⟨95855609881256654196179473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127807479841675538928239297 95855609881256654196179473)
              ·
                refine ⟨71891707410942490647134605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95855609881256654196179473 71891707410942490647134605)
                ·
                  refine ⟨26959390279103433992675477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71891707410942490647134605 26959390279103433992675477)
                  ·
                    refine ⟨1263721419332973468406663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26959390279103433992675477 1263721419332973468406663)
                    ·
                      rfl

theorem cell22_3691633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_3691633 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691633 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691633 prefixEnd_3691633 := by exact prefixLift 3691633
  have htrace : WordTrace (prefixWord ++ tailWord_3691633) baseStart_3691633 baseEnd_3691633 := by
    simpa [prefixWord, tailWord_3691633, baseEnd_3691633] using wordTrace_append hprefix tailTrace_3691633
  have hstable : (prefixWord ++ tailWord_3691633).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691633).length < 2 ^ (prefixWord ++ tailWord_3691633).sum := by decide
  have hdescent : baseEnd_3691633 < baseStart_3691633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691648 : List Nat := [2, 1, 1, 2, 1, 3, 3, 9]
def baseStart_3691648 : Nat := 118140960795 + 3691648 * 2 ^ 59
def prefixEnd_3691648 : Nat := 4983230072969 + 3 ^ 40 * 3691648 * 2
def baseEnd_3691648 : Nat := 140414061571057603253513

theorem tailTrace_3691648 : CollatzResearch.WordTrace tailWord_3691648 prefixEnd_3691648 140414061571057603253513 := by
  unfold tailWord_3691648
  simp only [CollatzResearch.WordTrace]
  refine ⟨67322732064898627064085799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89763642753198169418781065 67322732064898627064085799)
  ·
    refine ⟨100984098097347940596128699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67322732064898627064085799 100984098097347940596128699)
    ·
      refine ⟨151476147146021910894193049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100984098097347940596128699 151476147146021910894193049)
      ·
        refine ⟨113607110359516433170644787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 151476147146021910894193049 113607110359516433170644787)
        ·
          refine ⟨170410665539274649755967181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113607110359516433170644787 170410665539274649755967181)
          ·
            refine ⟨63903999577227993658487693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 170410665539274649755967181 63903999577227993658487693)
            ·
              refine ⟨23963999841460497621932885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63903999577227993658487693 23963999841460497621932885)
              ·
                refine ⟨140414061571057603253513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23963999841460497621932885 140414061571057603253513)
                ·
                  rfl

theorem cell22_3691648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 9].length) (baseStart_3691648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691648 prefixEnd_3691648 := by exact prefixLift 3691648
  have htrace : WordTrace (prefixWord ++ tailWord_3691648) baseStart_3691648 baseEnd_3691648 := by
    simpa [prefixWord, tailWord_3691648, baseEnd_3691648] using wordTrace_append hprefix tailTrace_3691648
  have hstable : (prefixWord ++ tailWord_3691648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691648).length < 2 ^ (prefixWord ++ tailWord_3691648).sum := by decide
  have hdescent : baseEnd_3691648 < baseStart_3691648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691656 : List Nat := [2, 1, 3, 4, 3, 1, 1, 2, 1, 4]
def baseStart_3691656 : Nat := 118140960795 + 3691656 * 2 ^ 59
def prefixEnd_3691656 : Nat := 4983230072969 + 3 ^ 40 * 3691656 * 2
def baseEnd_3691656 : Nat := 1263729292703009075081593

theorem tailTrace_3691656 : CollatzResearch.WordTrace tailWord_3691656 prefixEnd_3691656 1263729292703009075081593 := by
  unfold tailWord_3691656
  simp only [CollatzResearch.WordTrace]
  refine ⟨67322877956884135747231411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89763837275845514329641881 67322877956884135747231411)
  ·
    refine ⟨100984316935326203620847117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67322877956884135747231411 100984316935326203620847117)
    ·
      refine ⟨37869118850747326357817669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100984316935326203620847117 37869118850747326357817669)
      ·
        refine ⟨7100459784515123692090813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37869118850747326357817669 7100459784515123692090813)
        ·
          refine ⟨2662672419193171384534055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7100459784515123692090813 2662672419193171384534055)
          ·
            refine ⟨3994008628789757076801083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662672419193171384534055 3994008628789757076801083)
            ·
              refine ⟨5991012943184635615201625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3994008628789757076801083 5991012943184635615201625)
              ·
                refine ⟨4493259707388476711401219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5991012943184635615201625 4493259707388476711401219)
                ·
                  refine ⟨6739889561082715067101829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493259707388476711401219 6739889561082715067101829)
                  ·
                    refine ⟨1263729292703009075081593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6739889561082715067101829 1263729292703009075081593)
                    ·
                      rfl

theorem cell22_3691656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_3691656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691656 prefixEnd_3691656 := by exact prefixLift 3691656
  have htrace : WordTrace (prefixWord ++ tailWord_3691656) baseStart_3691656 baseEnd_3691656 := by
    simpa [prefixWord, tailWord_3691656, baseEnd_3691656] using wordTrace_append hprefix tailTrace_3691656
  have hstable : (prefixWord ++ tailWord_3691656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691656).length < 2 ^ (prefixWord ++ tailWord_3691656).sum := by decide
  have hdescent : baseEnd_3691656 < baseStart_3691656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691682 : List Nat := [3, 3, 1, 3, 3, 9]
def baseStart_3691682 : Nat := 118140960795 + 3691682 * 2 ^ 59
def prefixEnd_3691682 : Nat := 4983230072969 + 3 ^ 40 * 3691682 * 2
def baseEnd_3691682 : Nat := 15601706086843872517673

theorem tailTrace_3691682 : CollatzResearch.WordTrace tailWord_3691682 prefixEnd_3691682 15601706086843872517673 := by
  unfold tailWord_3691682
  simp only [CollatzResearch.WordTrace]
  refine ⟨33661676052918519483727325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89764469474449385289939533 33661676052918519483727325)
  ·
    refine ⟨12623128519844444806397747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33661676052918519483727325 12623128519844444806397747)
    ·
      refine ⟨18934692779766667209596621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12623128519844444806397747 18934692779766667209596621)
      ·
        refine ⟨7100509792412500203598733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18934692779766667209596621 7100509792412500203598733)
        ·
          refine ⟨2662691172154687576349525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7100509792412500203598733 2662691172154687576349525)
          ·
            refine ⟨15601706086843872517673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2662691172154687576349525 15601706086843872517673)
            ·
              rfl

theorem cell22_3691682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 9].length) (baseStart_3691682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691682 prefixEnd_3691682 := by exact prefixLift 3691682
  have htrace : WordTrace (prefixWord ++ tailWord_3691682) baseStart_3691682 baseEnd_3691682 := by
    simpa [prefixWord, tailWord_3691682, baseEnd_3691682] using wordTrace_append hprefix tailTrace_3691682
  have hstable : (prefixWord ++ tailWord_3691682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691682).length < 2 ^ (prefixWord ++ tailWord_3691682).sum := by decide
  have hdescent : baseEnd_3691682 < baseStart_3691682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691755 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 6]
def baseStart_3691755 : Nat := 118140960795 + 3691755 * 2 ^ 59
def prefixEnd_3691755 : Nat := 4983230072969 + 3 ^ 40 * 3691755 * 2
def baseEnd_3691755 : Nat := 421254394142068605618763

theorem tailTrace_3691755 : CollatzResearch.WordTrace tailWord_3691755 prefixEnd_3691755 421254394142068605618763 := by
  unfold tailWord_3691755
  simp only [CollatzResearch.WordTrace]
  refine ⟨134649366740409611402316719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89766244493606407601544479 134649366740409611402316719)
  ·
    refine ⟨201974050110614417103475079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134649366740409611402316719 201974050110614417103475079)
    ·
      refine ⟨302961075165921625655212619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201974050110614417103475079 302961075165921625655212619)
      ·
        refine ⟨454441612748882438482818929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302961075165921625655212619 454441612748882438482818929)
        ·
          refine ⟨340831209561661828862114197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 454441612748882438482818929 340831209561661828862114197)
          ·
            refine ⟨15976462948202898227911603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 340831209561661828862114197 15976462948202898227911603)
            ·
              refine ⟨23964694422304347341867405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15976462948202898227911603 23964694422304347341867405)
              ·
                refine ⟨8986760408364130253200277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23964694422304347341867405 8986760408364130253200277)
                ·
                  refine ⟨421254394142068605618763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8986760408364130253200277 421254394142068605618763)
                  ·
                    rfl

theorem cell22_3691755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 6].length) (baseStart_3691755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691755 prefixEnd_3691755 := by exact prefixLift 3691755
  have htrace : WordTrace (prefixWord ++ tailWord_3691755) baseStart_3691755 baseEnd_3691755 := by
    simpa [prefixWord, tailWord_3691755, baseEnd_3691755] using wordTrace_append hprefix tailTrace_3691755
  have hstable : (prefixWord ++ tailWord_3691755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691755).length < 2 ^ (prefixWord ++ tailWord_3691755).sum := by decide
  have hdescent : baseEnd_3691755 < baseStart_3691755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691774 : List Nat := [4, 2, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_3691774 : Nat := 118140960795 + 3691774 * 2 ^ 59
def prefixEnd_3691774 : Nat := 4983230072969 + 3 ^ 40 * 3691774 * 2
def baseEnd_3691774 : Nat := 1263769686514496100631231

theorem tailTrace_3691774 : CollatzResearch.WordTrace tailWord_3691774 prefixEnd_3691774 1263769686514496100631231 := by
  unfold tailWord_3691774
  simp only [CollatzResearch.WordTrace]
  refine ⟨16831257465917597205907297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 89766706484893851764838917 16831257465917597205907297)
  ·
    refine ⟨12623443099438197904430473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16831257465917597205907297 12623443099438197904430473)
    ·
      refine ⟨9467582324578648428322855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12623443099438197904430473 9467582324578648428322855)
      ·
        refine ⟨14201373486867972642484283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9467582324578648428322855 14201373486867972642484283)
        ·
          refine ⟨21302060230301958963726425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14201373486867972642484283 21302060230301958963726425)
          ·
            refine ⟨15976545172726469222794819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21302060230301958963726425 15976545172726469222794819)
            ·
              refine ⟨23964817759089703834192229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15976545172726469222794819 23964817759089703834192229)
              ·
                refine ⟨4493403329829319468911043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23964817759089703834192229 4493403329829319468911043)
                ·
                  refine ⟨6740104994743979203366565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4493403329829319468911043 6740104994743979203366565)
                  ·
                    refine ⟨1263769686514496100631231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6740104994743979203366565 1263769686514496100631231)
                    ·
                      rfl

theorem cell22_3691774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_3691774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691774 prefixEnd_3691774 := by exact prefixLift 3691774
  have htrace : WordTrace (prefixWord ++ tailWord_3691774) baseStart_3691774 baseEnd_3691774 := by
    simpa [prefixWord, tailWord_3691774, baseEnd_3691774] using wordTrace_append hprefix tailTrace_3691774
  have hstable : (prefixWord ++ tailWord_3691774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691774).length < 2 ^ (prefixWord ++ tailWord_3691774).sum := by decide
  have hdescent : baseEnd_3691774 < baseStart_3691774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691785 : List Nat := [1, 2, 1, 1, 3, 3, 1, 3, 1, 6]
def baseStart_3691785 : Nat := 118140960795 + 3691785 * 2 ^ 59
def prefixEnd_3691785 : Nat := 4983230072969 + 3 ^ 40 * 3691785 * 2
def baseEnd_3691785 : Nat := 1263773452039295738606197

theorem tailTrace_3691785 : CollatzResearch.WordTrace tailWord_3691785 prefixEnd_3691785 1263773452039295738606197 := by
  unfold tailWord_3691785
  simp only [CollatzResearch.WordTrace]
  refine ⟨134650460930300926525908809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89766973953533951017272539 134650460930300926525908809)
  ·
    refine ⟨100987845697725694894431607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 134650460930300926525908809 100987845697725694894431607)
    ·
      refine ⟨151481768546588542341647411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100987845697725694894431607 151481768546588542341647411)
      ·
        refine ⟨227222652819882813512471117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 151481768546588542341647411 227222652819882813512471117)
        ·
          refine ⟨85208494807456055067176669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 227222652819882813512471117 85208494807456055067176669)
          ·
            refine ⟨31953185552796020650191251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85208494807456055067176669 31953185552796020650191251)
            ·
              refine ⟨47929778329194030975286877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31953185552796020650191251 47929778329194030975286877)
              ·
                refine ⟨17973666873447761615732579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47929778329194030975286877 17973666873447761615732579)
                ·
                  refine ⟨26960500310171642423598869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17973666873447761615732579 26960500310171642423598869)
                  ·
                    refine ⟨1263773452039295738606197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26960500310171642423598869 1263773452039295738606197)
                    ·
                      rfl

theorem cell22_3691785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_3691785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691785 prefixEnd_3691785 := by exact prefixLift 3691785
  have htrace : WordTrace (prefixWord ++ tailWord_3691785) baseStart_3691785 baseEnd_3691785 := by
    simpa [prefixWord, tailWord_3691785, baseEnd_3691785] using wordTrace_append hprefix tailTrace_3691785
  have hstable : (prefixWord ++ tailWord_3691785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691785).length < 2 ^ (prefixWord ++ tailWord_3691785).sum := by decide
  have hdescent : baseEnd_3691785 < baseStart_3691785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691787 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 4, 3]
def baseStart_3691787 : Nat := 118140960795 + 3691787 * 2 ^ 59
def prefixEnd_3691787 : Nat := 4983230072969 + 3 ^ 40 * 3691787 * 2
def baseEnd_3691787 : Nat := 1263774136680168400056191

theorem tailTrace_3691787 : CollatzResearch.WordTrace tailWord_3691787 prefixEnd_3691787 1263774136680168400056191 := by
  unfold tailWord_3691787
  simp only [CollatzResearch.WordTrace]
  refine ⟨134650533876293680867481615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 89767022584195787244987743 134650533876293680867481615)
  ·
    refine ⟨201975800814440521301222423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 134650533876293680867481615 201975800814440521301222423)
    ·
      refine ⟨302963701221660781951833635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 201975800814440521301222423 302963701221660781951833635)
      ·
        refine ⟨454445551832491172927750453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 302963701221660781951833635 454445551832491172927750453)
        ·
          refine ⟨42604270484296047461976605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 454445551832491172927750453 42604270484296047461976605)
          ·
            refine ⟨15976601431611017798241227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42604270484296047461976605 15976601431611017798241227)
            ·
              refine ⟨23964902147416526697361841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15976601431611017798241227 23964902147416526697361841)
              ·
                refine ⟨17973676610562395023021381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23964902147416526697361841 17973676610562395023021381)
                ·
                  refine ⟨3370064364480449066816509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17973676610562395023021381 3370064364480449066816509)
                  ·
                    refine ⟨1263774136680168400056191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3370064364480449066816509 1263774136680168400056191)
                    ·
                      rfl

theorem cell22_3691787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 4, 3].length) (baseStart_3691787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691787 prefixEnd_3691787 := by exact prefixLift 3691787
  have htrace : WordTrace (prefixWord ++ tailWord_3691787) baseStart_3691787 baseEnd_3691787 := by
    simpa [prefixWord, tailWord_3691787, baseEnd_3691787] using wordTrace_append hprefix tailTrace_3691787
  have hstable : (prefixWord ++ tailWord_3691787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691787).length < 2 ^ (prefixWord ++ tailWord_3691787).sum := by decide
  have hdescent : baseEnd_3691787 < baseStart_3691787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691800 : List Nat := [2, 1, 2, 3, 1, 3, 10]
def baseStart_3691800 : Nat := 118140960795 + 3691800 * 2 ^ 59
def prefixEnd_3691800 : Nat := 4983230072969 + 3 ^ 40 * 3691800 * 2
def baseEnd_3691800 : Nat := 46806614327623729610413

theorem tailTrace_3691800 : CollatzResearch.WordTrace tailWord_3691800 prefixEnd_3691800 46806614327623729610413 := by
  unfold tailWord_3691800
  simp only [CollatzResearch.WordTrace]
  refine ⟨67325504012623292043852427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 89767338683497722725136569 67325504012623292043852427)
  ·
    refine ⟨100988256018934938065778641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67325504012623292043852427 100988256018934938065778641)
    ·
      refine ⟨75741192014201203549333981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100988256018934938065778641 75741192014201203549333981)
      ·
        refine ⟨28402947005325451331000243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75741192014201203549333981 28402947005325451331000243)
        ·
          refine ⟨42604420507988176996500365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28402947005325451331000243 42604420507988176996500365)
          ·
            refine ⟨15976657690495566373687637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42604420507988176996500365 15976657690495566373687637)
            ·
              refine ⟨46806614327623729610413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15976657690495566373687637 46806614327623729610413)
              ·
                rfl

theorem cell22_3691800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 10].length) (baseStart_3691800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691800 prefixEnd_3691800 := by exact prefixLift 3691800
  have htrace : WordTrace (prefixWord ++ tailWord_3691800) baseStart_3691800 baseEnd_3691800 := by
    simpa [prefixWord, tailWord_3691800, baseEnd_3691800] using wordTrace_append hprefix tailTrace_3691800
  have hstable : (prefixWord ++ tailWord_3691800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691800).length < 2 ^ (prefixWord ++ tailWord_3691800).sum := by decide
  have hdescent : baseEnd_3691800 < baseStart_3691800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3691802 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 4, 4]
def baseStart_3691802 : Nat := 118140960795 + 3691802 * 2 ^ 59
def prefixEnd_3691802 : Nat := 4983230072969 + 3 ^ 40 * 3691802 * 2
def baseEnd_3691802 : Nat := 1263779271486713360931145

theorem tailTrace_3691802 : CollatzResearch.WordTrace tailWord_3691802 prefixEnd_3691802 1263779271486713360931145 := by
  unfold tailWord_3691802
  simp only [CollatzResearch.WordTrace]
  refine ⟨33662770242809834607319415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 89767387314159558952851773 33662770242809834607319415)
  ·
    refine ⟨50494155364214751910979123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33662770242809834607319415 50494155364214751910979123)
    ·
      refine ⟨75741233046322127866468685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50494155364214751910979123 75741233046322127866468685)
      ·
        refine ⟨28402962392370797949925757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75741233046322127866468685 28402962392370797949925757)
        ·
          refine ⟨10651110897139049231222159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28402962392370797949925757 10651110897139049231222159)
          ·
            refine ⟨15976666345708573846833239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10651110897139049231222159 15976666345708573846833239)
            ·
              refine ⟨23964999518562860770249859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15976666345708573846833239 23964999518562860770249859)
              ·
                refine ⟨35947499277844291155374789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23964999518562860770249859 35947499277844291155374789)
                ·
                  refine ⟨6740156114595804591632773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35947499277844291155374789 6740156114595804591632773)
                  ·
                    refine ⟨1263779271486713360931145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6740156114595804591632773 1263779271486713360931145)
                    ·
                      rfl

theorem cell22_3691802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 4, 4].length) (baseStart_3691802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3691802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3691802 prefixEnd_3691802 := by exact prefixLift 3691802
  have htrace : WordTrace (prefixWord ++ tailWord_3691802) baseStart_3691802 baseEnd_3691802 := by
    simpa [prefixWord, tailWord_3691802, baseEnd_3691802] using wordTrace_append hprefix tailTrace_3691802
  have hstable : (prefixWord ++ tailWord_3691802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3691802).length < 2 ^ (prefixWord ++ tailWord_3691802).sum := by decide
  have hdescent : baseEnd_3691802 < baseStart_3691802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3691802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
