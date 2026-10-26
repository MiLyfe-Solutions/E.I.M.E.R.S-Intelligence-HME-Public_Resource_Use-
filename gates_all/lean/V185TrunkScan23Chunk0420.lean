import V185TrunkScan23Chunk0419

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2483250 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 6, 4]
def baseStart_2483250 : Nat := 118140960795 + 2483250 * 2 ^ 59
def prefixEnd_2483250 : Nat := 4983230072969 + 3 ^ 40 * 2483250 * 2
def baseEnd_2483250 : Nat := 425033611759171502218249

theorem tailTrace_2483250 : CollatzResearch.WordTrace tailWord_2483250 prefixEnd_2483250 425033611759171502218249 := by
  unfold tailWord_2483250
  simp only [CollatzResearch.WordTrace]
  refine ⟨22642892063404207545089801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60381045502411220120239469 22642892063404207545089801)
  ·
    refine ⟨16982169047553155658817351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22642892063404207545089801 16982169047553155658817351)
    ·
      refine ⟨25473253571329733488226027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16982169047553155658817351 25473253571329733488226027)
      ·
        refine ⟨38209880356994600232339041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25473253571329733488226027 38209880356994600232339041)
        ·
          refine ⟨28657410267745950174254281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38209880356994600232339041 28657410267745950174254281)
          ·
            refine ⟨21493057700809462630690711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28657410267745950174254281 21493057700809462630690711)
            ·
              refine ⟨32239586551214193946036067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21493057700809462630690711 32239586551214193946036067)
              ·
                refine ⟨48359379826821290919054101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32239586551214193946036067 48359379826821290919054101)
                ·
                  refine ⟨2266845929382248011830661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48359379826821290919054101 2266845929382248011830661)
                  ·
                    refine ⟨425033611759171502218249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2266845929382248011830661 425033611759171502218249)
                    ·
                      rfl

theorem cell23_2483250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_2483250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483250 prefixEnd_2483250 := by exact prefixLift 2483250
  have htrace : WordTrace (prefixWord ++ tailWord_2483250) baseStart_2483250 baseEnd_2483250 := by
    simpa [prefixWord, tailWord_2483250, baseEnd_2483250] using wordTrace_append hprefix tailTrace_2483250
  have hstable : (prefixWord ++ tailWord_2483250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483250).length < 2 ^ (prefixWord ++ tailWord_2483250).sum := by decide
  have hdescent : baseEnd_2483250 < baseStart_2483250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483257 : List Nat := [1, 2, 1, 5, 2, 1, 2, 3, 1, 1, 4]
def baseStart_2483257 : Nat := 118140960795 + 2483257 * 2 ^ 59
def prefixEnd_2483257 : Nat := 4983230072969 + 3 ^ 40 * 2483257 * 2
def baseEnd_2483257 : Nat := 1275104429642095979267215

theorem tailTrace_2483257 : CollatzResearch.WordTrace tailWord_2483257 prefixEnd_2483257 1275104429642095979267215 := by
  unfold tailWord_2483257
  simp only [CollatzResearch.WordTrace]
  refine ⟨90571823564591470375864025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60381215709727646917242683 90571823564591470375864025)
  ·
    refine ⟨67928867673443602781898019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90571823564591470375864025 67928867673443602781898019)
    ·
      refine ⟨101893301510165404172847029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67928867673443602781898019 101893301510165404172847029)
      ·
        refine ⟨9552497016578006641204409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101893301510165404172847029 9552497016578006641204409)
        ·
          refine ⟨7164372762433504980903307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9552497016578006641204409 7164372762433504980903307)
          ·
            refine ⟨10746559143650257471354961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7164372762433504980903307 10746559143650257471354961)
            ·
              refine ⟨8059919357737693103516221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10746559143650257471354961 8059919357737693103516221)
              ·
                refine ⟨3022469759151634913818583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8059919357737693103516221 3022469759151634913818583)
                ·
                  refine ⟨4533704638727452370727875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3022469759151634913818583 4533704638727452370727875)
                  ·
                    refine ⟨6800556958091178556091813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4533704638727452370727875 6800556958091178556091813)
                    ·
                      refine ⟨1275104429642095979267215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6800556958091178556091813 1275104429642095979267215)
                      ·
                        rfl

theorem cell23_2483257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_2483257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483257 prefixEnd_2483257 := by exact prefixLift 2483257
  have htrace : WordTrace (prefixWord ++ tailWord_2483257) baseStart_2483257 baseEnd_2483257 := by
    simpa [prefixWord, tailWord_2483257, baseEnd_2483257] using wordTrace_append hprefix tailTrace_2483257
  have hstable : (prefixWord ++ tailWord_2483257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483257).length < 2 ^ (prefixWord ++ tailWord_2483257).sum := by decide
  have hdescent : baseEnd_2483257 < baseStart_2483257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483260 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_2483260 : Nat := 118140960795 + 2483260 * 2 ^ 59
def prefixEnd_2483260 : Nat := 4983230072969 + 3 ^ 40 * 2483260 * 2
def baseEnd_2483260 : Nat := 1275105970084059467529701

theorem tailTrace_2483260 : CollatzResearch.WordTrace tailWord_2483260 prefixEnd_2483260 1275105970084059467529701 := by
  unfold tailWord_2483260
  simp only [CollatzResearch.WordTrace]
  refine ⟨45285966491790300944111617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60381288655720401258815489 45285966491790300944111617)
  ·
    refine ⟨33964474868842725708083713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45285966491790300944111617 33964474868842725708083713)
    ·
      refine ⟨25473356151632044281062785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33964474868842725708083713 25473356151632044281062785)
      ·
        refine ⟨19105017113724033210797089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25473356151632044281062785 19105017113724033210797089)
        ·
          refine ⟨14328762835293024908097817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19105017113724033210797089 14328762835293024908097817)
          ·
            refine ⟨10746572126469768681073363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14328762835293024908097817 10746572126469768681073363)
            ·
              refine ⟨16119858189704653021610045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10746572126469768681073363 16119858189704653021610045)
              ·
                refine ⟨6044946821139244883103767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16119858189704653021610045 6044946821139244883103767)
                ·
                  refine ⟨9067420231708867324655651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6044946821139244883103767 9067420231708867324655651)
                  ·
                    refine ⟨13601130347563300986983477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9067420231708867324655651 13601130347563300986983477)
                    ·
                      refine ⟨1275105970084059467529701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13601130347563300986983477 1275105970084059467529701)
                      ·
                        rfl

theorem cell23_2483260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_2483260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483260 prefixEnd_2483260 := by exact prefixLift 2483260
  have htrace : WordTrace (prefixWord ++ tailWord_2483260) baseStart_2483260 baseEnd_2483260 := by
    simpa [prefixWord, tailWord_2483260, baseEnd_2483260] using wordTrace_append hprefix tailTrace_2483260
  have hstable : (prefixWord ++ tailWord_2483260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483260).length < 2 ^ (prefixWord ++ tailWord_2483260).sum := by decide
  have hdescent : baseEnd_2483260 < baseStart_2483260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483274 : List Nat := [3, 1, 2, 1, 1, 2, 5, 1, 3, 2, 2]
def baseStart_2483274 : Nat := 118140960795 + 2483274 * 2 ^ 59
def prefixEnd_2483274 : Nat := 4983230072969 + 3 ^ 40 * 2483274 * 2
def baseEnd_2483274 : Nat := 1275113158813222412754637

theorem tailTrace_2483274 : CollatzResearch.WordTrace tailWord_2483274 prefixEnd_2483274 1275113158813222412754637 := by
  unfold tailWord_2483274
  simp only [CollatzResearch.WordTrace]
  refine ⟨22643110901382470569808219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60381629070353254852821917 22643110901382470569808219)
  ·
    refine ⟨33964666352073705854712329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22643110901382470569808219 33964666352073705854712329)
    ·
      refine ⟨25473499764055279391034247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33964666352073705854712329 25473499764055279391034247)
      ·
        refine ⟨38210249646082919086551371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25473499764055279391034247 38210249646082919086551371)
        ·
          refine ⟨57315374469124378629827057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38210249646082919086551371 57315374469124378629827057)
          ·
            refine ⟨42986530851843283972370293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57315374469124378629827057 42986530851843283972370293)
            ·
              refine ⟨4029987267360307872409715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42986530851843283972370293 4029987267360307872409715)
              ·
                refine ⟨6044980901040461808614573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4029987267360307872409715 6044980901040461808614573)
                ·
                  refine ⟨2266867837890173178230465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6044980901040461808614573 2266867837890173178230465)
                  ·
                    refine ⟨1700150878417629883672849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2266867837890173178230465 1700150878417629883672849)
                    ·
                      refine ⟨1275113158813222412754637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700150878417629883672849 1275113158813222412754637)
                      ·
                        rfl

theorem cell23_2483274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_2483274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483274 prefixEnd_2483274 := by exact prefixLift 2483274
  have htrace : WordTrace (prefixWord ++ tailWord_2483274) baseStart_2483274 baseEnd_2483274 := by
    simpa [prefixWord, tailWord_2483274, baseEnd_2483274] using wordTrace_append hprefix tailTrace_2483274
  have hstable : (prefixWord ++ tailWord_2483274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483274).length < 2 ^ (prefixWord ++ tailWord_2483274).sum := by decide
  have hdescent : baseEnd_2483274 < baseStart_2483274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483277 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 1, 1, 5]
def baseStart_2483277 : Nat := 118140960795 + 2483277 * 2 ^ 59
def prefixEnd_2483277 : Nat := 4983230072969 + 3 ^ 40 * 2483277 * 2
def baseEnd_2483277 : Nat := 1275114699255185901017123

theorem tailTrace_2483277 : CollatzResearch.WordTrace tailWord_2483277 prefixEnd_2483277 1275114699255185901017123 := by
  unfold tailWord_2483277
  simp only [CollatzResearch.WordTrace]
  refine ⟨90572553024519013791592085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60381702016346009194394723 90572553024519013791592085)
  ·
    refine ⟨4245588423024328771480879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 90572553024519013791592085 4245588423024328771480879)
    ·
      refine ⟨6368382634536493157221319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4245588423024328771480879 6368382634536493157221319)
      ·
        refine ⟨9552573951804739735831979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6368382634536493157221319 9552573951804739735831979)
        ·
          refine ⟨14328860927707109603747969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9552573951804739735831979 14328860927707109603747969)
          ·
            refine ⟨10746645695780332202810977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14328860927707109603747969 10746645695780332202810977)
            ·
              refine ⟨8059984271835249152108233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10746645695780332202810977 8059984271835249152108233)
              ·
                refine ⟨6044988203876436864081175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8059984271835249152108233 6044988203876436864081175)
                ·
                  refine ⟨9067482305814655296121763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6044988203876436864081175 9067482305814655296121763)
                  ·
                    refine ⟨13601223458721982944182645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9067482305814655296121763 13601223458721982944182645)
                    ·
                      refine ⟨1275114699255185901017123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13601223458721982944182645 1275114699255185901017123)
                      ·
                        rfl

theorem cell23_2483277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_2483277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483277 prefixEnd_2483277 := by exact prefixLift 2483277
  have htrace : WordTrace (prefixWord ++ tailWord_2483277) baseStart_2483277 baseEnd_2483277 := by
    simpa [prefixWord, tailWord_2483277, baseEnd_2483277] using wordTrace_append hprefix tailTrace_2483277
  have hstable : (prefixWord ++ tailWord_2483277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483277).length < 2 ^ (prefixWord ++ tailWord_2483277).sum := by decide
  have hdescent : baseEnd_2483277 < baseStart_2483277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483284 : List Nat := [2, 4, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_2483284 : Nat := 118140960795 + 2483284 * 2 ^ 59
def prefixEnd_2483284 : Nat := 4983230072969 + 3 ^ 40 * 2483284 * 2
def baseEnd_2483284 : Nat := 425039431206589124543197

theorem tailTrace_2483284 : CollatzResearch.WordTrace tailWord_2483284 prefixEnd_2483284 425039431206589124543197 := by
  unfold tailWord_2483284
  simp only [CollatzResearch.WordTrace]
  refine ⟨45286404167746826993548453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60381872223662435991397937 45286404167746826993548453)
  ·
    refine ⟨8491200781452530061290335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45286404167746826993548453 8491200781452530061290335)
    ·
      refine ⟨12736801172178795091935503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8491200781452530061290335 12736801172178795091935503)
      ·
        refine ⟨19105201758268192637903255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12736801172178795091935503 19105201758268192637903255)
        ·
          refine ⟨28657802637402288956854883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19105201758268192637903255 28657802637402288956854883)
          ·
            refine ⟨42986703956103433435282325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28657802637402288956854883 42986703956103433435282325)
            ·
              refine ⟨2015001747942348442278859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 42986703956103433435282325 2015001747942348442278859)
              ·
                refine ⟨3022502621913522663418289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015001747942348442278859 3022502621913522663418289)
                ·
                  refine ⟨2266876966435141997563717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3022502621913522663418289 2266876966435141997563717)
                  ·
                    refine ⟨425039431206589124543197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2266876966435141997563717 425039431206589124543197)
                    ·
                      rfl

theorem cell23_2483284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_2483284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483284 prefixEnd_2483284 := by exact prefixLift 2483284
  have htrace : WordTrace (prefixWord ++ tailWord_2483284) baseStart_2483284 baseEnd_2483284 := by
    simpa [prefixWord, tailWord_2483284, baseEnd_2483284] using wordTrace_append hprefix tailTrace_2483284
  have hstable : (prefixWord ++ tailWord_2483284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483284).length < 2 ^ (prefixWord ++ tailWord_2483284).sum := by decide
  have hdescent : baseEnd_2483284 < baseStart_2483284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483304 : List Nat := [2, 1, 4, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2483304 : Nat := 118140960795 + 2483304 * 2 ^ 59
def prefixEnd_2483304 : Nat := 4983230072969 + 3 ^ 40 * 2483304 * 2
def baseEnd_2483304 : Nat := 1275128563232857295379499

theorem tailTrace_2483304 : CollatzResearch.WordTrace tailWord_2483304 prefixEnd_2483304 1275128563232857295379499 := by
  unfold tailWord_2483304
  simp only [CollatzResearch.WordTrace]
  refine ⟨45286768897710598701412483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60382358530280798268549977 45286768897710598701412483)
  ·
    refine ⟨67930153346565898052118725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45286768897710598701412483 67930153346565898052118725)
    ·
      refine ⟨12736903752481105884772261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67930153346565898052118725 12736903752481105884772261)
      ·
        refine ⟨2388169453590207353394799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12736903752481105884772261 2388169453590207353394799)
        ·
          refine ⟨3582254180385311030092199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2388169453590207353394799 3582254180385311030092199)
          ·
            refine ⟨5373381270577966545138299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3582254180385311030092199 5373381270577966545138299)
            ·
              refine ⟨8060071905866949817707449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5373381270577966545138299 8060071905866949817707449)
              ·
                refine ⟨6045053929400212363280587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8060071905866949817707449 6045053929400212363280587)
                ·
                  refine ⟨9067580894100318544920881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6045053929400212363280587 9067580894100318544920881)
                  ·
                    refine ⟨6800685670575238908690661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9067580894100318544920881 6800685670575238908690661)
                    ·
                      refine ⟨1275128563232857295379499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6800685670575238908690661 1275128563232857295379499)
                      ·
                        rfl

theorem cell23_2483304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2483304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483304 prefixEnd_2483304 := by exact prefixLift 2483304
  have htrace : WordTrace (prefixWord ++ tailWord_2483304) baseStart_2483304 baseEnd_2483304 := by
    simpa [prefixWord, tailWord_2483304, baseEnd_2483304] using wordTrace_append hprefix tailTrace_2483304
  have hstable : (prefixWord ++ tailWord_2483304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483304).length < 2 ^ (prefixWord ++ tailWord_2483304).sum := by decide
  have hdescent : baseEnd_2483304 < baseStart_2483304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483323 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 3, 8]
def baseStart_2483323 : Nat := 118140960795 + 2483323 * 2 ^ 59
def prefixEnd_2483323 : Nat := 4983230072969 + 3 ^ 40 * 2483323 * 2
def baseEnd_2483323 : Nat := 425046106455097573680637

theorem tailTrace_2483323 : CollatzResearch.WordTrace tailWord_2483323 prefixEnd_2483323 425046106455097573680637 := by
  unfold tailWord_2483323
  simp only [CollatzResearch.WordTrace]
  refine ⟨90574230782352363647766623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60382820521568242431844415 90574230782352363647766623)
  ·
    refine ⟨135861346173528545471649935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90574230782352363647766623 135861346173528545471649935)
    ·
      refine ⟨203792019260292818207474903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135861346173528545471649935 203792019260292818207474903)
      ·
        refine ⟨305688028890439227311212355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203792019260292818207474903 305688028890439227311212355)
        ·
          refine ⟨458532043335658840966818533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305688028890439227311212355 458532043335658840966818533)
          ·
            refine ⟨85974758125436032681278475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 458532043335658840966818533 85974758125436032681278475)
            ·
              refine ⟨128962137188154049021917713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85974758125436032681278475 128962137188154049021917713)
              ·
                refine ⟨96721602891115536766438285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128962137188154049021917713 96721602891115536766438285)
                ·
                  refine ⟨36270601084168326287414357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96721602891115536766438285 36270601084168326287414357)
                  ·
                    refine ⟨425046106455097573680637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36270601084168326287414357 425046106455097573680637)
                    ·
                      rfl

theorem cell23_2483323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 8].length) (baseStart_2483323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483323 prefixEnd_2483323 := by exact prefixLift 2483323
  have htrace : WordTrace (prefixWord ++ tailWord_2483323) baseStart_2483323 baseEnd_2483323 := by
    simpa [prefixWord, tailWord_2483323, baseEnd_2483323] using wordTrace_append hprefix tailTrace_2483323
  have hstable : (prefixWord ++ tailWord_2483323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483323).length < 2 ^ (prefixWord ++ tailWord_2483323).sum := by decide
  have hdescent : baseEnd_2483323 < baseStart_2483323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483324 : List Nat := [2, 2, 2, 1, 1, 3, 4, 2, 2, 1, 3]
def baseStart_2483324 : Nat := 118140960795 + 2483324 * 2 ^ 59
def prefixEnd_2483324 : Nat := 4983230072969 + 3 ^ 40 * 2483324 * 2
def baseEnd_2483324 : Nat := 1275138832845947217129407

theorem tailTrace_2483324 : CollatzResearch.WordTrace tailWord_2483324 prefixEnd_2483324 1275138832845947217129407 := by
  unfold tailWord_2483324
  simp only [CollatzResearch.WordTrace]
  refine ⟨45287133627674370409276513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60382844836899160545702017 45287133627674370409276513)
  ·
    refine ⟨33965350220755777806957385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45287133627674370409276513 33965350220755777806957385)
    ·
      refine ⟨25474012665566833355218039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33965350220755777806957385 25474012665566833355218039)
      ·
        refine ⟨38211018998350250032827059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25474012665566833355218039 38211018998350250032827059)
        ·
          refine ⟨57316528497525375049240589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38211018998350250032827059 57316528497525375049240589)
          ·
            refine ⟨21493698186572015643465221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57316528497525375049240589 21493698186572015643465221)
            ·
              refine ⟨4030068409982252933149729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21493698186572015643465221 4030068409982252933149729)
              ·
                refine ⟨3022551307486689699862297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4030068409982252933149729 3022551307486689699862297)
                ·
                  refine ⟨2266913480615017274896723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3022551307486689699862297 2266913480615017274896723)
                  ·
                    refine ⟨3400370220922525912345085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2266913480615017274896723 3400370220922525912345085)
                    ·
                      refine ⟨1275138832845947217129407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3400370220922525912345085 1275138832845947217129407)
                      ·
                        rfl

theorem cell23_2483324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_2483324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483324 prefixEnd_2483324 := by exact prefixLift 2483324
  have htrace : WordTrace (prefixWord ++ tailWord_2483324) baseStart_2483324 baseEnd_2483324 := by
    simpa [prefixWord, tailWord_2483324, baseEnd_2483324] using wordTrace_append hprefix tailTrace_2483324
  have hstable : (prefixWord ++ tailWord_2483324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483324).length < 2 ^ (prefixWord ++ tailWord_2483324).sum := by decide
  have hdescent : baseEnd_2483324 < baseStart_2483324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483347 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 1, 4, 2]
def baseStart_2483347 : Nat := 118140960795 + 2483347 * 2 ^ 59
def prefixEnd_2483347 : Nat := 4983230072969 + 3 ^ 40 * 2483347 * 2
def baseEnd_2483347 : Nat := 1275150642901000627141801

theorem tailTrace_2483347 : CollatzResearch.WordTrace tailWord_2483347 prefixEnd_2483347 1275150642901000627141801 := by
  unfold tailWord_2483347
  simp only [CollatzResearch.WordTrace]
  refine ⟨90575106134265415746640295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60383404089510277164426863 90575106134265415746640295)
  ·
    refine ⟨135862659201398123619960443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90575106134265415746640295 135862659201398123619960443)
    ·
      refine ⟨203793988802097185429940665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135862659201398123619960443 203793988802097185429940665)
      ·
        refine ⟨152845491601572889072455499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203793988802097185429940665 152845491601572889072455499)
        ·
          refine ⟨229268237402359333608683249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152845491601572889072455499 229268237402359333608683249)
          ·
            refine ⟨171951178051769500206512437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229268237402359333608683249 171951178051769500206512437)
            ·
              refine ⟨16120422942353390644360541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 171951178051769500206512437 16120422942353390644360541)
              ·
                refine ⟨6045158603382521491635203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16120422942353390644360541 6045158603382521491635203)
                ·
                  refine ⟨9067737905073782237452805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6045158603382521491635203 9067737905073782237452805)
                  ·
                    refine ⟨1700200857201334169522401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9067737905073782237452805 1700200857201334169522401)
                    ·
                      refine ⟨1275150642901000627141801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700200857201334169522401 1275150642901000627141801)
                      ·
                        rfl

theorem cell23_2483347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 4, 2].length) (baseStart_2483347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483347 prefixEnd_2483347 := by exact prefixLift 2483347
  have htrace : WordTrace (prefixWord ++ tailWord_2483347) baseStart_2483347 baseEnd_2483347 := by
    simpa [prefixWord, tailWord_2483347, baseEnd_2483347] using wordTrace_append hprefix tailTrace_2483347
  have hstable : (prefixWord ++ tailWord_2483347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483347).length < 2 ^ (prefixWord ++ tailWord_2483347).sum := by decide
  have hdescent : baseEnd_2483347 < baseStart_2483347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483360 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 4]
def baseStart_2483360 : Nat := 118140960795 + 2483360 * 2 ^ 59
def prefixEnd_2483360 : Nat := 4983230072969 + 3 ^ 40 * 2483360 * 2
def baseEnd_2483360 : Nat := 1275157318149509076279241

theorem tailTrace_2483360 : CollatzResearch.WordTrace tailWord_2483360 prefixEnd_2483360 1275157318149509076279241 := by
  unfold tailWord_2483360
  simp only [CollatzResearch.WordTrace]
  refine ⟨45287790141609159483431767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60383720188812212644575689 45287790141609159483431767)
  ·
    refine ⟨67931685212413739225147651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45287790141609159483431767 67931685212413739225147651)
    ·
      refine ⟨101897527818620608837721477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67931685212413739225147651 101897527818620608837721477)
      ·
        refine ⟨19105786465991364157072777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101897527818620608837721477 19105786465991364157072777)
        ·
          refine ⟨14329339849493523117804583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19105786465991364157072777 14329339849493523117804583)
          ·
            refine ⟨21494009774240284676706875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14329339849493523117804583 21494009774240284676706875)
            ·
              refine ⟨32241014661360427015060313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21494009774240284676706875 32241014661360427015060313)
              ·
                refine ⟨24180760996020320261295235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32241014661360427015060313 24180760996020320261295235)
                ·
                  refine ⟨36271141494030480391942853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24180760996020320261295235 36271141494030480391942853)
                  ·
                    refine ⟨6800839030130715073489285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36271141494030480391942853 6800839030130715073489285)
                    ·
                      refine ⟨1275157318149509076279241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6800839030130715073489285 1275157318149509076279241)
                      ·
                        rfl

theorem cell23_2483360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_2483360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483360 prefixEnd_2483360 := by exact prefixLift 2483360
  have htrace : WordTrace (prefixWord ++ tailWord_2483360) baseStart_2483360 baseEnd_2483360 := by
    simpa [prefixWord, tailWord_2483360, baseEnd_2483360] using wordTrace_append hprefix tailTrace_2483360
  have hstable : (prefixWord ++ tailWord_2483360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483360).length < 2 ^ (prefixWord ++ tailWord_2483360).sum := by decide
  have hdescent : baseEnd_2483360 < baseStart_2483360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483364 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 1, 4, 2]
def baseStart_2483364 : Nat := 118140960795 + 2483364 * 2 ^ 59
def prefixEnd_2483364 : Nat := 4983230072969 + 3 ^ 40 * 2483364 * 2
def baseEnd_2483364 : Nat := 1275159372072127060629223

theorem tailTrace_2483364 : CollatzResearch.WordTrace tailWord_2483364 prefixEnd_2483364 1275159372072127060629223 := by
  unfold tailWord_2483364
  simp only [CollatzResearch.WordTrace]
  refine ⟨45287863087601913825004573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60383817450135885100006097 45287863087601913825004573)
  ·
    refine ⟨16982948657850717684376715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45287863087601913825004573 16982948657850717684376715)
    ·
      refine ⟨25474422986776076526565073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16982948657850717684376715 25474422986776076526565073)
      ·
        refine ⟨19105817240082057394923805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25474422986776076526565073 19105817240082057394923805)
        ·
          refine ⟨7164681465030771523096427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19105817240082057394923805 7164681465030771523096427)
          ·
            refine ⟨10747022197546157284644641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7164681465030771523096427 10747022197546157284644641)
            ·
              refine ⟨8060266648159617963483481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10747022197546157284644641 8060266648159617963483481)
              ·
                refine ⟨6045199986119713472612611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8060266648159617963483481 6045199986119713472612611)
                ·
                  refine ⟨9067799979179570208918917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6045199986119713472612611 9067799979179570208918917)
                  ·
                    refine ⟨1700212496096169414172297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9067799979179570208918917 1700212496096169414172297)
                    ·
                      refine ⟨1275159372072127060629223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700212496096169414172297 1275159372072127060629223)
                      ·
                        rfl

theorem cell23_2483364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_2483364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483364 prefixEnd_2483364 := by exact prefixLift 2483364
  have htrace : WordTrace (prefixWord ++ tailWord_2483364) baseStart_2483364 baseEnd_2483364 := by
    simpa [prefixWord, tailWord_2483364, baseEnd_2483364] using wordTrace_append hprefix tailTrace_2483364
  have hstable : (prefixWord ++ tailWord_2483364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483364).length < 2 ^ (prefixWord ++ tailWord_2483364).sum := by decide
  have hdescent : baseEnd_2483364 < baseStart_2483364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483377 : List Nat := [1, 2, 2, 5, 1, 1, 1, 2, 2, 2, 4]
def baseStart_2483377 : Nat := 118140960795 + 2483377 * 2 ^ 59
def prefixEnd_2483377 : Nat := 4983230072969 + 3 ^ 40 * 2483377 * 2
def baseEnd_2483377 : Nat := 1275166047320635509766663

theorem tailTrace_2483377 : CollatzResearch.WordTrace tailWord_2483377 prefixEnd_2483377 1275166047320635509766663 := by
  unfold tailWord_2483377
  simp only [CollatzResearch.WordTrace]
  refine ⟨90576200324156730870232385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60384133549437820580154923 90576200324156730870232385)
  ·
    refine ⟨67932150243117548152674289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90576200324156730870232385 67932150243117548152674289)
    ·
      refine ⟨50949112682338161114505717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67932150243117548152674289 50949112682338161114505717)
      ·
        refine ⟨4776479313969202604484911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50949112682338161114505717 4776479313969202604484911)
        ·
          refine ⟨7164718970953803906727367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4776479313969202604484911 7164718970953803906727367)
          ·
            refine ⟨10747078456430705860091051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7164718970953803906727367 10747078456430705860091051)
            ·
              refine ⟨16120617684646058790136577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10747078456430705860091051 16120617684646058790136577)
              ·
                refine ⟨12090463263484544092602433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16120617684646058790136577 12090463263484544092602433)
                ·
                  refine ⟨9067847447613408069451825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12090463263484544092602433 9067847447613408069451825)
                  ·
                    refine ⟨6800885585710056052088869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9067847447613408069451825 6800885585710056052088869)
                    ·
                      refine ⟨1275166047320635509766663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6800885585710056052088869 1275166047320635509766663)
                      ·
                        rfl

theorem cell23_2483377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_2483377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483377 prefixEnd_2483377 := by exact prefixLift 2483377
  have htrace : WordTrace (prefixWord ++ tailWord_2483377) baseStart_2483377 baseEnd_2483377 := by
    simpa [prefixWord, tailWord_2483377, baseEnd_2483377] using wordTrace_append hprefix tailTrace_2483377
  have hstable : (prefixWord ++ tailWord_2483377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483377).length < 2 ^ (prefixWord ++ tailWord_2483377).sum := by decide
  have hdescent : baseEnd_2483377 < baseStart_2483377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483400 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 1, 7]
def baseStart_2483400 : Nat := 118140960795 + 2483400 * 2 ^ 59
def prefixEnd_2483400 : Nat := 4983230072969 + 3 ^ 40 * 2483400 * 2
def baseEnd_2483400 : Nat := 425059285791896306593019

theorem tailTrace_2483400 : CollatzResearch.WordTrace tailWord_2483400 prefixEnd_2483400 425059285791896306593019 := by
  unfold tailWord_2483400
  simp only [CollatzResearch.WordTrace]
  refine ⟨45288519601536702899159827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60384692802048937198879769 45288519601536702899159827)
  ·
    refine ⟨67932779402305054348739741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45288519601536702899159827 67932779402305054348739741)
    ·
      refine ⟨25474792275864395380777403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67932779402305054348739741 25474792275864395380777403)
      ·
        refine ⟨38212188413796593071166105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25474792275864395380777403 38212188413796593071166105)
        ·
          refine ⟨28659141310347444803374579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38212188413796593071166105 28659141310347444803374579)
          ·
            refine ⟨42988711965521167205061869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28659141310347444803374579 42988711965521167205061869)
            ·
              refine ⟨16120766987070437701898201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42988711965521167205061869 16120766987070437701898201)
              ·
                refine ⟨12090575240302828276423651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16120766987070437701898201 12090575240302828276423651)
                ·
                  refine ⟨18135862860454242414635477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12090575240302828276423651 18135862860454242414635477)
                  ·
                    refine ⟨425059285791896306593019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18135862860454242414635477 425059285791896306593019)
                    ·
                      rfl

theorem cell23_2483400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_2483400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483400 prefixEnd_2483400 := by exact prefixLift 2483400
  have htrace : WordTrace (prefixWord ++ tailWord_2483400) baseStart_2483400 baseEnd_2483400 := by
    simpa [prefixWord, tailWord_2483400, baseEnd_2483400] using wordTrace_append hprefix tailTrace_2483400
  have hstable : (prefixWord ++ tailWord_2483400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483400).length < 2 ^ (prefixWord ++ tailWord_2483400).sum := by decide
  have hdescent : baseEnd_2483400 < baseStart_2483400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483498 : List Nat := [3, 1, 4, 2, 1, 2, 1, 4, 1, 4]
def baseStart_2483498 : Nat := 118140960795 + 2483498 * 2 ^ 59
def prefixEnd_2483498 : Nat := 4983230072969 + 3 ^ 40 * 2483498 * 2
def baseEnd_2483498 : Nat := 425076059493276512117869

theorem tailTrace_2483498 : CollatzResearch.WordTrace tailWord_2483498 prefixEnd_2483498 425076059493276512117869 := by
  unfold tailWord_2483498
  simp only [CollatzResearch.WordTrace]
  refine ⟨22645153389179592133846787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60387075704478912356924765 22645153389179592133846787)
  ·
    refine ⟨33967730083769388200770181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22645153389179592133846787 33967730083769388200770181)
    ·
      refine ⟨6368949390706760287644409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33967730083769388200770181 6368949390706760287644409)
      ·
        refine ⟨4776712043030070215733307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6368949390706760287644409 4776712043030070215733307)
        ·
          refine ⟨7165068064545105323599961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4776712043030070215733307 7165068064545105323599961)
          ·
            refine ⟨5373801048408828992699971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7165068064545105323599961 5373801048408828992699971)
            ·
              refine ⟨8060701572613243489049957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5373801048408828992699971 8060701572613243489049957)
              ·
                refine ⟨1511381544864983154196867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8060701572613243489049957 1511381544864983154196867)
                ·
                  refine ⟨2267072317297474731295301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511381544864983154196867 2267072317297474731295301)
                  ·
                    refine ⟨425076059493276512117869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2267072317297474731295301 425076059493276512117869)
                    ·
                      rfl

theorem cell23_2483498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_2483498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483498 prefixEnd_2483498 := by exact prefixLift 2483498
  have htrace : WordTrace (prefixWord ++ tailWord_2483498) baseStart_2483498 baseEnd_2483498 := by
    simpa [prefixWord, tailWord_2483498, baseEnd_2483498] using wordTrace_append hprefix tailTrace_2483498
  have hstable : (prefixWord ++ tailWord_2483498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483498).length < 2 ^ (prefixWord ++ tailWord_2483498).sum := by decide
  have hdescent : baseEnd_2483498 < baseStart_2483498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483504 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 3, 1, 3]
def baseStart_2483504 : Nat := 118140960795 + 2483504 * 2 ^ 59
def prefixEnd_2483504 : Nat := 4983230072969 + 3 ^ 40 * 2483504 * 2
def baseEnd_2483504 : Nat := 1275231259363756512878579

theorem tailTrace_2483504 : CollatzResearch.WordTrace tailWord_2483504 prefixEnd_2483504 1275231259363756512878579 := by
  unfold tailWord_2483504
  simp only [CollatzResearch.WordTrace]
  refine ⟨45290416197348315780052783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60387221596464421040070377 45290416197348315780052783)
  ·
    refine ⟨67935624296022473670079175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45290416197348315780052783 67935624296022473670079175)
    ·
      refine ⟨101903436444033710505118763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67935624296022473670079175 101903436444033710505118763)
      ·
        refine ⟨152855154666050565757678145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101903436444033710505118763 152855154666050565757678145)
        ·
          refine ⟨114641365999537924318258609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152855154666050565757678145 114641365999537924318258609)
          ·
            refine ⟨85981024499653443238693957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114641365999537924318258609 85981024499653443238693957)
            ·
              refine ⟨16121442093685020607255117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85981024499653443238693957 16121442093685020607255117)
              ·
                refine ⟨6045540785131882727720669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16121442093685020607255117 6045540785131882727720669)
                ·
                  refine ⟨2267077794424456022895251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6045540785131882727720669 2267077794424456022895251)
                  ·
                    refine ⟨3400616691636684034342877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2267077794424456022895251 3400616691636684034342877)
                    ·
                      refine ⟨1275231259363756512878579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3400616691636684034342877 1275231259363756512878579)
                      ·
                        rfl

theorem cell23_2483504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 3, 1, 3].length) (baseStart_2483504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483504 prefixEnd_2483504 := by exact prefixLift 2483504
  have htrace : WordTrace (prefixWord ++ tailWord_2483504) baseStart_2483504 baseEnd_2483504 := by
    simpa [prefixWord, tailWord_2483504, baseEnd_2483504] using wordTrace_append hprefix tailTrace_2483504
  have hstable : (prefixWord ++ tailWord_2483504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483504).length < 2 ^ (prefixWord ++ tailWord_2483504).sum := by decide
  have hdescent : baseEnd_2483504 < baseStart_2483504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483507 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 3, 5]
def baseStart_2483507 : Nat := 118140960795 + 2483507 * 2 ^ 59
def prefixEnd_2483507 : Nat := 4983230072969 + 3 ^ 40 * 2483507 * 2
def baseEnd_2483507 : Nat := 425077599935240000380355

theorem tailTrace_2483507 : CollatzResearch.WordTrace tailWord_2483507 prefixEnd_2483507 425077599935240000380355 := by
  unfold tailWord_2483507
  simp only [CollatzResearch.WordTrace]
  refine ⟨90580941813685763072464775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60387294542457175381643183 90580941813685763072464775)
  ·
    refine ⟨135871412720528644608697163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90580941813685763072464775 135871412720528644608697163)
    ·
      refine ⟨203807119080792966913045745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135871412720528644608697163 203807119080792966913045745)
      ·
        refine ⟨152855339310594725184784309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203807119080792966913045745 152855339310594725184784309)
        ·
          refine ⟨14330188060368255486073529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152855339310594725184784309 14330188060368255486073529)
          ·
            refine ⟨10747641045276191614555147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14330188060368255486073529 10747641045276191614555147)
            ·
              refine ⟨16121461567914287421832721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10747641045276191614555147 16121461567914287421832721)
              ·
                refine ⟨12091096175935715566374541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16121461567914287421832721 12091096175935715566374541)
                ·
                  refine ⟨4534161065975893337390453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12091096175935715566374541 4534161065975893337390453)
                  ·
                    refine ⟨425077599935240000380355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4534161065975893337390453 425077599935240000380355)
                    ·
                      rfl

theorem cell23_2483507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 5].length) (baseStart_2483507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483507 prefixEnd_2483507 := by exact prefixLift 2483507
  have htrace : WordTrace (prefixWord ++ tailWord_2483507) baseStart_2483507 baseEnd_2483507 := by
    simpa [prefixWord, tailWord_2483507, baseEnd_2483507] using wordTrace_append hprefix tailTrace_2483507
  have hstable : (prefixWord ++ tailWord_2483507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483507).length < 2 ^ (prefixWord ++ tailWord_2483507).sum := by decide
  have hdescent : baseEnd_2483507 < baseStart_2483507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483514 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2]
def baseStart_2483514 : Nat := 118140960795 + 2483514 * 2 ^ 59
def prefixEnd_2483514 : Nat := 4983230072969 + 3 ^ 40 * 2483514 * 2
def baseEnd_2483514 : Nat := 1275236394170301473753533

theorem tailTrace_2483514 : CollatzResearch.WordTrace tailWord_2483514 prefixEnd_2483514 1275236394170301473753533 := by
  unfold tailWord_2483514
  simp only [CollatzResearch.WordTrace]
  refine ⟨22645299281165100816992399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60387464749773602178646397 22645299281165100816992399)
  ·
    refine ⟨33967948921747651225488599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22645299281165100816992399 33967948921747651225488599)
    ·
      refine ⟨50951923382621476838232899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33967948921747651225488599 50951923382621476838232899)
      ·
        refine ⟨76427885073932215257349349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50951923382621476838232899 76427885073932215257349349)
        ·
          refine ⟨14330228451362290360753003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76427885073932215257349349 14330228451362290360753003)
          ·
            refine ⟨21495342677043435541129505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14330228451362290360753003 21495342677043435541129505)
            ·
              refine ⟨16121507007782576655847129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21495342677043435541129505 16121507007782576655847129)
              ·
                refine ⟨12091130255836932491885347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16121507007782576655847129 12091130255836932491885347)
                ·
                  refine ⟨18136695383755398737828021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12091130255836932491885347 18136695383755398737828021)
                  ·
                    refine ⟨1700315192227068631671377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18136695383755398737828021 1700315192227068631671377)
                    ·
                      refine ⟨1275236394170301473753533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700315192227068631671377 1275236394170301473753533)
                      ·
                        rfl

theorem cell23_2483514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2].length) (baseStart_2483514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483514 prefixEnd_2483514 := by exact prefixLift 2483514
  have htrace : WordTrace (prefixWord ++ tailWord_2483514) baseStart_2483514 baseEnd_2483514 := by
    simpa [prefixWord, tailWord_2483514, baseEnd_2483514] using wordTrace_append hprefix tailTrace_2483514
  have hstable : (prefixWord ++ tailWord_2483514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483514).length < 2 ^ (prefixWord ++ tailWord_2483514).sum := by decide
  have hdescent : baseEnd_2483514 < baseStart_2483514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483521 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 5, 1, 3]
def baseStart_2483521 : Nat := 118140960795 + 2483521 * 2 ^ 59
def prefixEnd_2483521 : Nat := 4983230072969 + 3 ^ 40 * 2483521 * 2
def baseEnd_2483521 : Nat := 1275239988534882946366001

theorem tailTrace_2483521 : CollatzResearch.WordTrace tailWord_2483521 prefixEnd_2483521 1275239988534882946366001 := by
  unfold tailWord_2483521
  simp only [CollatzResearch.WordTrace]
  refine ⟨90581452435635043463474417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60387634957090028975649611 90581452435635043463474417)
  ·
    refine ⟨67936089326726282597605813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90581452435635043463474417 67936089326726282597605813)
    ·
      refine ⟨6369008374380588993525545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67936089326726282597605813 6369008374380588993525545)
      ·
        refine ⟨4776756280785441745144159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6369008374380588993525545 4776756280785441745144159)
        ·
          refine ⟨7165134421178162617716239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4776756280785441745144159 7165134421178162617716239)
          ·
            refine ⟨10747701631767243926574359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7165134421178162617716239 10747701631767243926574359)
            ·
              refine ⟨16121552447650865889861539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10747701631767243926574359 16121552447650865889861539)
              ·
                refine ⟨24182328671476298834792309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16121552447650865889861539 24182328671476298834792309)
                ·
                  refine ⟨2267093312950903015761779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24182328671476298834792309 2267093312950903015761779)
                  ·
                    refine ⟨3400639969426354523642669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2267093312950903015761779 3400639969426354523642669)
                    ·
                      refine ⟨1275239988534882946366001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3400639969426354523642669 1275239988534882946366001)
                      ·
                        rfl

theorem cell23_2483521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_2483521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483521 prefixEnd_2483521 := by exact prefixLift 2483521
  have htrace : WordTrace (prefixWord ++ tailWord_2483521) baseStart_2483521 baseEnd_2483521 := by
    simpa [prefixWord, tailWord_2483521, baseEnd_2483521] using wordTrace_append hprefix tailTrace_2483521
  have hstable : (prefixWord ++ tailWord_2483521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483521).length < 2 ^ (prefixWord ++ tailWord_2483521).sum := by decide
  have hdescent : baseEnd_2483521 < baseStart_2483521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483537 : List Nat := [1, 2, 2, 1, 4, 1, 1, 4, 1, 6]
def baseStart_2483537 : Nat := 118140960795 + 2483537 * 2 ^ 59
def prefixEnd_2483537 : Nat := 4983230072969 + 3 ^ 40 * 2483537 * 2
def baseEnd_2483537 : Nat := 425082734741784961255309

theorem tailTrace_2483537 : CollatzResearch.WordTrace tailWord_2483537 prefixEnd_2483537 425082734741784961255309 := by
  unfold tailWord_2483537
  simp only [CollatzResearch.WordTrace]
  refine ⟨90582036003577078196056865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60388024002384718797371243 90582036003577078196056865)
  ·
    refine ⟨67936527002682808647042649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90582036003577078196056865 67936527002682808647042649)
    ·
      refine ⟨50952395252012106485281987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67936527002682808647042649 50952395252012106485281987)
      ·
        refine ⟨76428592878018159727922981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50952395252012106485281987 76428592878018159727922981)
        ·
          refine ⟨14330361164628404948985559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76428592878018159727922981 14330361164628404948985559)
          ·
            refine ⟨21495541746942607423478339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14330361164628404948985559 21495541746942607423478339)
            ·
              refine ⟨32243312620413911135217509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21495541746942607423478339 32243312620413911135217509)
              ·
                refine ⟨6045621116327608337853283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32243312620413911135217509 6045621116327608337853283)
                ·
                  refine ⟨9068431674491412506779925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6045621116327608337853283 9068431674491412506779925)
                  ·
                    refine ⟨425082734741784961255309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9068431674491412506779925 425082734741784961255309)
                    ·
                      rfl

theorem cell23_2483537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 6].length) (baseStart_2483537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483537 prefixEnd_2483537 := by exact prefixLift 2483537
  have htrace : WordTrace (prefixWord ++ tailWord_2483537) baseStart_2483537 baseEnd_2483537 := by
    simpa [prefixWord, tailWord_2483537, baseEnd_2483537] using wordTrace_append hprefix tailTrace_2483537
  have hstable : (prefixWord ++ tailWord_2483537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483537).length < 2 ^ (prefixWord ++ tailWord_2483537).sum := by decide
  have hdescent : baseEnd_2483537 < baseStart_2483537 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483541 : List Nat := [1, 3, 2, 2, 3, 1, 4, 1, 1, 5]
def baseStart_2483541 : Nat := 118140960795 + 2483541 * 2 ^ 59
def prefixEnd_2483541 : Nat := 4983230072969 + 3 ^ 40 * 2483541 * 2
def baseEnd_2483541 : Nat := 425083419382657622705303

theorem tailTrace_2483541 : CollatzResearch.WordTrace tailWord_2483541 prefixEnd_2483541 425083419382657622705303 := by
  unfold tailWord_2483541
  simp only [CollatzResearch.WordTrace]
  refine ⟨90582181895562586879202477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60388121263708391252801651 90582181895562586879202477)
  ·
    refine ⟨33968318210835970079700929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90582181895562586879202477 33968318210835970079700929)
    ·
      refine ⟨25476238658126977559775697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33968318210835970079700929 25476238658126977559775697)
      ·
        refine ⟨19107178993595233169831773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25476238658126977559775697 19107178993595233169831773)
        ·
          refine ⟨7165192122598212438686915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19107178993595233169831773 7165192122598212438686915)
          ·
            refine ⟨10747788183897318658030373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7165192122598212438686915 10747788183897318658030373)
            ·
              refine ⟨2015210284480747248380695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10747788183897318658030373 2015210284480747248380695)
              ·
                refine ⟨3022815426721120872571043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015210284480747248380695 3022815426721120872571043)
                ·
                  refine ⟨4534223140081681308856565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3022815426721120872571043 4534223140081681308856565)
                  ·
                    refine ⟨425083419382657622705303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4534223140081681308856565 425083419382657622705303)
                    ·
                      rfl

theorem cell23_2483541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_2483541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483541 prefixEnd_2483541 := by exact prefixLift 2483541
  have htrace : WordTrace (prefixWord ++ tailWord_2483541) baseStart_2483541 baseEnd_2483541 := by
    simpa [prefixWord, tailWord_2483541, baseEnd_2483541] using wordTrace_append hprefix tailTrace_2483541
  have hstable : (prefixWord ++ tailWord_2483541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483541).length < 2 ^ (prefixWord ++ tailWord_2483541).sum := by decide
  have hdescent : baseEnd_2483541 < baseStart_2483541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483544 : List Nat := [2, 1, 2, 2, 1, 1, 5, 3, 1, 1, 4]
def baseStart_2483544 : Nat := 118140960795 + 2483544 * 2 ^ 59
def prefixEnd_2483544 : Nat := 4983230072969 + 3 ^ 40 * 2483544 * 2
def baseEnd_2483544 : Nat := 1275251798589936356378395

theorem tailTrace_2483544 : CollatzResearch.WordTrace tailWord_2483544 prefixEnd_2483544 1275251798589936356378395 := by
  unfold tailWord_2483544
  simp only [CollatzResearch.WordTrace]
  refine ⟨45291145657275859195780843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60388194209701145594374457 45291145657275859195780843)
  ·
    refine ⟨67936718485913788793671265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45291145657275859195780843 67936718485913788793671265)
    ·
      refine ⟨50952538864435341595253449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67936718485913788793671265 50952538864435341595253449)
      ·
        refine ⟨38214404148326506196440087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50952538864435341595253449 38214404148326506196440087)
        ·
          refine ⟨57321606222489759294660131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38214404148326506196440087 57321606222489759294660131)
          ·
            refine ⟨85982409333734638941990197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57321606222489759294660131 85982409333734638941990197)
            ·
              refine ⟨8060850875037622400811581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85982409333734638941990197 8060850875037622400811581)
              ·
                refine ⟨3022819078139108400304343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8060850875037622400811581 3022819078139108400304343)
                ·
                  refine ⟨4534228617208662600456515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3022819078139108400304343 4534228617208662600456515)
                  ·
                    refine ⟨6801342925812993900684773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4534228617208662600456515 6801342925812993900684773)
                    ·
                      refine ⟨1275251798589936356378395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6801342925812993900684773 1275251798589936356378395)
                      ·
                        rfl

theorem cell23_2483544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_2483544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483544 prefixEnd_2483544 := by exact prefixLift 2483544
  have htrace : WordTrace (prefixWord ++ tailWord_2483544) baseStart_2483544 baseEnd_2483544 := by
    simpa [prefixWord, tailWord_2483544, baseEnd_2483544] using wordTrace_append hprefix tailTrace_2483544
  have hstable : (prefixWord ++ tailWord_2483544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483544).length < 2 ^ (prefixWord ++ tailWord_2483544).sum := by decide
  have hdescent : baseEnd_2483544 < baseStart_2483544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483557 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 1, 1, 6]
def baseStart_2483557 : Nat := 118140960795 + 2483557 * 2 ^ 59
def prefixEnd_2483557 : Nat := 4983230072969 + 3 ^ 40 * 2483557 * 2
def baseEnd_2483557 : Nat := 1275258473838444805515835

theorem tailTrace_2483557 : CollatzResearch.WordTrace tailWord_2483557 prefixEnd_2483557 1275258473838444805515835 := by
  unfold tailWord_2483557
  simp only [CollatzResearch.WordTrace]
  refine ⟨90582765463504621611784925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60388510309003081074523283 90582765463504621611784925)
  ·
    refine ⟨33968537048814233104419347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90582765463504621611784925 33968537048814233104419347)
    ·
      refine ⟨50952805573221349656629021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33968537048814233104419347 50952805573221349656629021)
      ·
        refine ⟨19107302089958006121235883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50952805573221349656629021 19107302089958006121235883)
        ·
          refine ⟨28660953134937009181853825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19107302089958006121235883 28660953134937009181853825)
          ·
            refine ⟨21495714851202756886390369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28660953134937009181853825 21495714851202756886390369)
            ·
              refine ⟨16121786138402067664792777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21495714851202756886390369 16121786138402067664792777)
              ·
                refine ⟨12091339603801550748594583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16121786138402067664792777 12091339603801550748594583)
                ·
                  refine ⟨18137009405702326122891875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12091339603801550748594583 18137009405702326122891875)
                  ·
                    refine ⟨27205514108553489184337813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18137009405702326122891875 27205514108553489184337813)
                    ·
                      refine ⟨1275258473838444805515835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27205514108553489184337813 1275258473838444805515835)
                      ·
                        rfl

theorem cell23_2483557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_2483557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483557 prefixEnd_2483557 := by exact prefixLift 2483557
  have htrace : WordTrace (prefixWord ++ tailWord_2483557) baseStart_2483557 baseEnd_2483557 := by
    simpa [prefixWord, tailWord_2483557, baseEnd_2483557] using wordTrace_append hprefix tailTrace_2483557
  have hstable : (prefixWord ++ tailWord_2483557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483557).length < 2 ^ (prefixWord ++ tailWord_2483557).sum := by decide
  have hdescent : baseEnd_2483557 < baseStart_2483557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483564 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 5]
def baseStart_2483564 : Nat := 118140960795 + 2483564 * 2 ^ 59
def prefixEnd_2483564 : Nat := 4983230072969 + 3 ^ 40 * 2483564 * 2
def baseEnd_2483564 : Nat := 1275262068203026278128303

theorem tailTrace_2483564 : CollatzResearch.WordTrace tailWord_2483564 prefixEnd_2483564 1275262068203026278128303 := by
  unfold tailWord_2483564
  simp only [CollatzResearch.WordTrace]
  refine ⟨45291510387239630903644873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60388680516319507871526497 45291510387239630903644873)
  ·
    refine ⟨33968632790429723177733655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45291510387239630903644873 33968632790429723177733655)
    ·
      refine ⟨50952949185644584766600483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33968632790429723177733655 50952949185644584766600483)
      ·
        refine ⟨76429423778466877149900725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50952949185644584766600483 76429423778466877149900725)
        ·
          refine ⟨7165258479231269732803193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76429423778466877149900725 7165258479231269732803193)
          ·
            refine ⟨5373943859423452299602395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7165258479231269732803193 5373943859423452299602395)
            ·
              refine ⟨8060915789135178449403593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5373943859423452299602395 8060915789135178449403593)
              ·
                refine ⟨6045686841851383837052695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8060915789135178449403593 6045686841851383837052695)
                ·
                  refine ⟨9068530262777075755579043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6045686841851383837052695 9068530262777075755579043)
                  ·
                    refine ⟨13602795394165613633368565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9068530262777075755579043 13602795394165613633368565)
                    ·
                      refine ⟨1275262068203026278128303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13602795394165613633368565 1275262068203026278128303)
                      ·
                        rfl

theorem cell23_2483564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_2483564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483564 prefixEnd_2483564 := by exact prefixLift 2483564
  have htrace : WordTrace (prefixWord ++ tailWord_2483564) baseStart_2483564 baseEnd_2483564 := by
    simpa [prefixWord, tailWord_2483564, baseEnd_2483564] using wordTrace_append hprefix tailTrace_2483564
  have hstable : (prefixWord ++ tailWord_2483564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483564).length < 2 ^ (prefixWord ++ tailWord_2483564).sum := by decide
  have hdescent : baseEnd_2483564 < baseStart_2483564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483581 : List Nat := [1, 4, 1, 1, 2, 2, 4, 2, 1, 2, 3]
def baseStart_2483581 : Nat := 118140960795 + 2483581 * 2 ^ 59
def prefixEnd_2483581 : Nat := 4983230072969 + 3 ^ 40 * 2483581 * 2
def baseEnd_2483581 : Nat := 1275270797374152711615725

theorem tailTrace_2483581 : CollatzResearch.WordTrace tailWord_2483581 prefixEnd_2483581 1275270797374152711615725 := by
  unfold tailWord_2483581
  simp only [CollatzResearch.WordTrace]
  refine ⟨90583640815417673710658597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60389093876945115807105731 90583640815417673710658597)
  ·
    refine ⟨16984432652890813820748487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90583640815417673710658597 16984432652890813820748487)
    ·
      refine ⟨25476648979336220731122731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16984432652890813820748487 25476648979336220731122731)
      ·
        refine ⟨38214973469004331096684097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25476648979336220731122731 38214973469004331096684097)
        ·
          refine ⟨28661230101753248322513073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38214973469004331096684097 28661230101753248322513073)
          ·
            refine ⟨21495922576314936241884805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28661230101753248322513073 21495922576314936241884805)
            ·
              refine ⟨4030485483059050545353401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21495922576314936241884805 4030485483059050545353401)
              ·
                refine ⟨3022864112294287909015051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4030485483059050545353401 3022864112294287909015051)
                ·
                  refine ⟨4534296168441431863522577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3022864112294287909015051 4534296168441431863522577)
                  ·
                    refine ⟨3400722126331073897641933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4534296168441431863522577 3400722126331073897641933)
                    ·
                      refine ⟨1275270797374152711615725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3400722126331073897641933 1275270797374152711615725)
                      ·
                        rfl

theorem cell23_2483581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_2483581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483581 prefixEnd_2483581 := by exact prefixLift 2483581
  have htrace : WordTrace (prefixWord ++ tailWord_2483581) baseStart_2483581 baseEnd_2483581 := by
    simpa [prefixWord, tailWord_2483581, baseEnd_2483581] using wordTrace_append hprefix tailTrace_2483581
  have hstable : (prefixWord ++ tailWord_2483581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483581).length < 2 ^ (prefixWord ++ tailWord_2483581).sum := by decide
  have hdescent : baseEnd_2483581 < baseStart_2483581 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483607 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 5]
def baseStart_2483607 : Nat := 118140960795 + 2483607 * 2 ^ 59
def prefixEnd_2483607 : Nat := 4983230072969 + 3 ^ 40 * 2483607 * 2
def baseEnd_2483607 : Nat := 1275284147871169609890605

theorem tailTrace_2483607 : CollatzResearch.WordTrace tailWord_2483607 prefixEnd_2483607 1275284147871169609890605 := by
  unfold tailWord_2483607
  simp only [CollatzResearch.WordTrace]
  refine ⟨90584589113323480151105075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60389726075548986767403383 90584589113323480151105075)
  ·
    refine ⟨135876883669985220226657613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90584589113323480151105075 135876883669985220226657613)
    ·
      refine ⟨50953831376244457584996605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135876883669985220226657613 50953831376244457584996605)
      ·
        refine ⟨19107686766091671594373727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50953831376244457584996605 19107686766091671594373727)
        ·
          refine ⟨28661530149137507391560591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19107686766091671594373727 28661530149137507391560591)
          ·
            refine ⟨42992295223706261087340887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28661530149137507391560591 42992295223706261087340887)
            ·
              refine ⟨64488442835559391631011331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42992295223706261087340887 64488442835559391631011331)
              ·
                refine ⟨96732664253339087446516997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64488442835559391631011331 96732664253339087446516997)
                ·
                  refine ⟨18137374547501078896221937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96732664253339087446516997 18137374547501078896221937)
                  ·
                    refine ⟨13603030910625809172166453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18137374547501078896221937 13603030910625809172166453)
                    ·
                      refine ⟨1275284147871169609890605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13603030910625809172166453 1275284147871169609890605)
                      ·
                        rfl

theorem cell23_2483607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_2483607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483607 prefixEnd_2483607 := by exact prefixLift 2483607
  have htrace : WordTrace (prefixWord ++ tailWord_2483607) baseStart_2483607 baseEnd_2483607 := by
    simpa [prefixWord, tailWord_2483607, baseEnd_2483607] using wordTrace_append hprefix tailTrace_2483607
  have hstable : (prefixWord ++ tailWord_2483607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483607).length < 2 ^ (prefixWord ++ tailWord_2483607).sum := by decide
  have hdescent : baseEnd_2483607 < baseStart_2483607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483612 : List Nat := [2, 2, 3, 4, 1, 2, 1, 1, 3, 2, 2]
def baseStart_2483612 : Nat := 118140960795 + 2483612 * 2 ^ 59
def prefixEnd_2483612 : Nat := 4983230072969 + 3 ^ 40 * 2483612 * 2
def baseEnd_2483612 : Nat := 1275286715274442090328083

theorem tailTrace_2483612 : CollatzResearch.WordTrace tailWord_2483612 prefixEnd_2483612 1275286715274442090328083 := by
  unfold tailWord_2483612
  simp only [CollatzResearch.WordTrace]
  refine ⟨45292385739152683002518545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60389847652203577336691393 45292385739152683002518545)
  ·
    refine ⟨33969289304364512251888909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45292385739152683002518545 33969289304364512251888909)
    ·
      refine ⟨12738483489136692094458341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33969289304364512251888909 12738483489136692094458341)
      ·
        refine ⟨2388465654213129767710939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12738483489136692094458341 2388465654213129767710939)
        ·
          refine ⟨3582698481319694651566409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2388465654213129767710939 3582698481319694651566409)
          ·
            refine ⟨2687023860989770988674807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3582698481319694651566409 2687023860989770988674807)
            ·
              refine ⟨4030535791484656483012211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2687023860989770988674807 4030535791484656483012211)
              ·
                refine ⟨6045803687226984724518317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4030535791484656483012211 6045803687226984724518317)
                ·
                  refine ⟨2267176382710119271694369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6045803687226984724518317 2267176382710119271694369)
                  ·
                    refine ⟨1700382287032589453770777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2267176382710119271694369 1700382287032589453770777)
                    ·
                      refine ⟨1275286715274442090328083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700382287032589453770777 1275286715274442090328083)
                      ·
                        rfl

theorem cell23_2483612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_2483612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483612 prefixEnd_2483612 := by exact prefixLift 2483612
  have htrace : WordTrace (prefixWord ++ tailWord_2483612) baseStart_2483612 baseEnd_2483612 := by
    simpa [prefixWord, tailWord_2483612, baseEnd_2483612] using wordTrace_append hprefix tailTrace_2483612
  have hstable : (prefixWord ++ tailWord_2483612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483612).length < 2 ^ (prefixWord ++ tailWord_2483612).sum := by decide
  have hdescent : baseEnd_2483612 < baseStart_2483612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483628 : List Nat := [2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 3]
def baseStart_2483628 : Nat := 118140960795 + 2483628 * 2 ^ 59
def prefixEnd_2483628 : Nat := 4983230072969 + 3 ^ 40 * 2483628 * 2
def baseEnd_2483628 : Nat := 1275294930964914027728009

theorem tailTrace_2483628 : CollatzResearch.WordTrace tailWord_2483628 prefixEnd_2483628 1275294930964914027728009 := by
  unfold tailWord_2483628
  simp only [CollatzResearch.WordTrace]
  refine ⟨45292677523123700368809769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60390236697498267158413025 45292677523123700368809769)
  ·
    refine ⟨33969508142342775276607327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45292677523123700368809769 33969508142342775276607327)
    ·
      refine ⟨50954262213514162914910991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33969508142342775276607327 50954262213514162914910991)
      ·
        refine ⟨76431393320271244372366487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50954262213514162914910991 76431393320271244372366487)
        ·
          refine ⟨114647089980406866558549731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76431393320271244372366487 114647089980406866558549731)
          ·
            refine ⟨171970634970610299837824597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114647089980406866558549731 171970634970610299837824597)
            ·
              refine ⟨2015280878561839451224507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 171970634970610299837824597 2015280878561839451224507)
              ·
                refine ⟨3022921317842759176836761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015280878561839451224507 3022921317842759176836761)
                ·
                  refine ⟨2267190988382069382627571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3022921317842759176836761 2267190988382069382627571)
                  ·
                    refine ⟨3400786482573104073941357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2267190988382069382627571 3400786482573104073941357)
                    ·
                      refine ⟨1275294930964914027728009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3400786482573104073941357 1275294930964914027728009)
                      ·
                        rfl

theorem cell23_2483628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 3].length) (baseStart_2483628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483628 prefixEnd_2483628 := by exact prefixLift 2483628
  have htrace : WordTrace (prefixWord ++ tailWord_2483628) baseStart_2483628 baseEnd_2483628 := by
    simpa [prefixWord, tailWord_2483628, baseEnd_2483628] using wordTrace_append hprefix tailTrace_2483628
  have hstable : (prefixWord ++ tailWord_2483628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483628).length < 2 ^ (prefixWord ++ tailWord_2483628).sum := by decide
  have hdescent : baseEnd_2483628 < baseStart_2483628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483651 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 6, 2, 2]
def baseStart_2483651 : Nat := 118140960795 + 2483651 * 2 ^ 59
def prefixEnd_2483651 : Nat := 4983230072969 + 3 ^ 40 * 2483651 * 2
def baseEnd_2483651 : Nat := 1275306741019967437740403

theorem tailTrace_2483651 : CollatzResearch.WordTrace tailWord_2483651 prefixEnd_2483651 1275306741019967437740403 := by
  unfold tailWord_2483651
  simp only [CollatzResearch.WordTrace]
  refine ⟨90586193925164075665706807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60390795950109383777137871 90586193925164075665706807)
  ·
    refine ⟨135879290887746113498560211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90586193925164075665706807 135879290887746113498560211)
    ·
      refine ⟨203818936331619170247840317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135879290887746113498560211 203818936331619170247840317)
      ·
        refine ⟨76432101124357188842940119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203818936331619170247840317 76432101124357188842940119)
        ·
          refine ⟨114648151686535783264410179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76432101124357188842940119 114648151686535783264410179)
          ·
            refine ⟨171972227529803674896615269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114648151686535783264410179 171972227529803674896615269)
            ·
              refine ⟨32244792661838189043115363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171972227529803674896615269 32244792661838189043115363)
              ·
                refine ⟨48367188992757283564673045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32244792661838189043115363 48367188992757283564673045)
                ·
                  refine ⟨2267211984035497667094049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48367188992757283564673045 2267211984035497667094049)
                  ·
                    refine ⟨1700408988026623250320537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2267211984035497667094049 1700408988026623250320537)
                    ·
                      refine ⟨1275306741019967437740403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700408988026623250320537 1275306741019967437740403)
                      ·
                        rfl

theorem cell23_2483651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 2, 2].length) (baseStart_2483651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483651 prefixEnd_2483651 := by exact prefixLift 2483651
  have htrace : WordTrace (prefixWord ++ tailWord_2483651) baseStart_2483651 baseEnd_2483651 := by
    simpa [prefixWord, tailWord_2483651, baseEnd_2483651] using wordTrace_append hprefix tailTrace_2483651
  have hstable : (prefixWord ++ tailWord_2483651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483651).length < 2 ^ (prefixWord ++ tailWord_2483651).sum := by decide
  have hdescent : baseEnd_2483651 < baseStart_2483651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483685 : List Nat := [1, 3, 1, 5, 1, 1, 2, 3, 2, 2, 2]
def baseStart_2483685 : Nat := 118140960795 + 2483685 * 2 ^ 59
def prefixEnd_2483685 : Nat := 4983230072969 + 3 ^ 40 * 2483685 * 2
def baseEnd_2483685 : Nat := 1275324199362220304715247

theorem tailTrace_2483685 : CollatzResearch.WordTrace tailWord_2483685 prefixEnd_2483685 1275324199362220304715247 := by
  unfold tailWord_2483685
  simp only [CollatzResearch.WordTrace]
  refine ⟨90587434007040899472444509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60391622671360599648296339 90587434007040899472444509)
  ·
    refine ⟨33970287752640337302166691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90587434007040899472444509 33970287752640337302166691)
    ·
      refine ⟨50955431628960505953250037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33970287752640337302166691 50955431628960505953250037)
      ·
        refine ⟨4777071715215047433117191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50955431628960505953250037 4777071715215047433117191)
        ·
          refine ⟨7165607572822571149675787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4777071715215047433117191 7165607572822571149675787)
          ·
            refine ⟨10748411359233856724513681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7165607572822571149675787 10748411359233856724513681)
            ·
              refine ⟨8061308519425392543385261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10748411359233856724513681 8061308519425392543385261)
              ·
                refine ⟨3022990694784522203769473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8061308519425392543385261 3022990694784522203769473)
                ·
                  refine ⟨2267243021088391652827105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3022990694784522203769473 2267243021088391652827105)
                  ·
                    refine ⟨1700432265816293739620329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2267243021088391652827105 1700432265816293739620329)
                    ·
                      refine ⟨1275324199362220304715247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700432265816293739620329 1275324199362220304715247)
                      ·
                        rfl

theorem cell23_2483685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_2483685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483685 prefixEnd_2483685 := by exact prefixLift 2483685
  have htrace : WordTrace (prefixWord ++ tailWord_2483685) baseStart_2483685 baseEnd_2483685 := by
    simpa [prefixWord, tailWord_2483685, baseEnd_2483685] using wordTrace_append hprefix tailTrace_2483685
  have hstable : (prefixWord ++ tailWord_2483685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483685).length < 2 ^ (prefixWord ++ tailWord_2483685).sum := by decide
  have hdescent : baseEnd_2483685 < baseStart_2483685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483704 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 1, 7]
def baseStart_2483704 : Nat := 118140960795 + 2483704 * 2 ^ 59
def prefixEnd_2483704 : Nat := 4983230072969 + 3 ^ 40 * 2483704 * 2
def baseEnd_2483704 : Nat := 425111318498218576792553

theorem tailTrace_2483704 : CollatzResearch.WordTrace tailWord_2483704 prefixEnd_2483704 425111318498218576792553 := by
  unfold tailWord_2483704
  simp only [CollatzResearch.WordTrace]
  refine ⟨45294063496986032858693083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60392084662648043811590777 45294063496986032858693083)
  ·
    refine ⟨67941095245479049288039625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45294063496986032858693083 67941095245479049288039625)
    ·
      refine ⟨50955821434109286966029719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67941095245479049288039625 50955821434109286966029719)
      ·
        refine ⟨76433732151163930449044579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50955821434109286966029719 76433732151163930449044579)
        ·
          refine ⟨114650598226745895673566869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76433732151163930449044579 114650598226745895673566869)
          ·
            refine ⟨5374246791878713859698447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 114650598226745895673566869 5374246791878713859698447)
            ·
              refine ⟨8061370187818070789547671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5374246791878713859698447 8061370187818070789547671)
              ·
                refine ⟨12092055281727106184321507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8061370187818070789547671 12092055281727106184321507)
                ·
                  refine ⟨18138082922590659276482261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12092055281727106184321507 18138082922590659276482261)
                  ·
                    refine ⟨425111318498218576792553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18138082922590659276482261 425111318498218576792553)
                    ·
                      rfl

theorem cell23_2483704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_2483704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483704 prefixEnd_2483704 := by exact prefixLift 2483704
  have htrace : WordTrace (prefixWord ++ tailWord_2483704) baseStart_2483704 baseEnd_2483704 := by
    simpa [prefixWord, tailWord_2483704, baseEnd_2483704] using wordTrace_append hprefix tailTrace_2483704
  have hstable : (prefixWord ++ tailWord_2483704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483704).length < 2 ^ (prefixWord ++ tailWord_2483704).sum := by decide
  have hdescent : baseEnd_2483704 < baseStart_2483704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483725 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 7]
def baseStart_2483725 : Nat := 118140960795 + 2483725 * 2 ^ 59
def prefixEnd_2483725 : Nat := 4983230072969 + 3 ^ 40 * 2483725 * 2
def baseEnd_2483725 : Nat := 141704970954266683135007

theorem tailTrace_2483725 : CollatzResearch.WordTrace tailWord_2483725 prefixEnd_2483725 141704970954266683135007 := by
  unfold tailWord_2483725
  simp only [CollatzResearch.WordTrace]
  refine ⟨90588892926895986303900629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60392595284597324202600419 90588892926895986303900629)
  ·
    refine ⟨2123177177974124678997671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 90588892926895986303900629 2123177177974124678997671)
    ·
      refine ⟨3184765766961187018496507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2123177177974124678997671 3184765766961187018496507)
      ·
        refine ⟨4777148650441780527744761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3184765766961187018496507 4777148650441780527744761)
        ·
          refine ⟨3582861487831335395808571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4777148650441780527744761 3582861487831335395808571)
          ·
            refine ⟨5374292231747003093712857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3582861487831335395808571 5374292231747003093712857)
            ·
              refine ⟨4030719173810252320284643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5374292231747003093712857 4030719173810252320284643)
              ·
                refine ⟨6046078760715378480426965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4030719173810252320284643 6046078760715378480426965)
                ·
                  refine ⟨141704970954266683135007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6046078760715378480426965 141704970954266683135007)
                  ·
                    rfl

theorem cell23_2483725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_2483725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483725 prefixEnd_2483725 := by exact prefixLift 2483725
  have htrace : WordTrace (prefixWord ++ tailWord_2483725) baseStart_2483725 baseEnd_2483725 := by
    simpa [prefixWord, tailWord_2483725, baseEnd_2483725] using wordTrace_append hprefix tailTrace_2483725
  have hstable : (prefixWord ++ tailWord_2483725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483725).length < 2 ^ (prefixWord ++ tailWord_2483725).sum := by decide
  have hdescent : baseEnd_2483725 < baseStart_2483725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483761 : List Nat := [1, 2, 2, 3, 1, 1, 1, 5, 2, 2, 3]
def baseStart_2483761 : Nat := 118140960795 + 2483761 * 2 ^ 59
def prefixEnd_2483761 : Nat := 4983230072969 + 3 ^ 40 * 2483761 * 2
def baseEnd_2483761 : Nat := 1275363223891962007364897

theorem tailTrace_2483761 : CollatzResearch.WordTrace tailWord_2483761 prefixEnd_2483761 1275363223891962007364897 := by
  unfold tailWord_2483761
  simp only [CollatzResearch.WordTrace]
  refine ⟨90590205954765564452211137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60393470636510376301474091 90590205954765564452211137)
  ·
    refine ⟨67942654466074173339158353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90590205954765564452211137 67942654466074173339158353)
    ·
      refine ⟨50956990849555630004368765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67942654466074173339158353 50956990849555630004368765)
      ·
        refine ⟨19108871568583361251638287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50956990849555630004368765 19108871568583361251638287)
        ·
          refine ⟨28663307352875041877457431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19108871568583361251638287 28663307352875041877457431)
          ·
            refine ⟨42994961029312562816186147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28663307352875041877457431 42994961029312562816186147)
            ·
              refine ⟨64492441543968844224279221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42994961029312562816186147 64492441543968844224279221)
              ·
                refine ⟨6046166394747079146026177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64492441543968844224279221 6046166394747079146026177)
                ·
                  refine ⟨4534624796060309359519633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6046166394747079146026177 4534624796060309359519633)
                  ·
                    refine ⟨3400968597045232019639725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4534624796060309359519633 3400968597045232019639725)
                    ·
                      refine ⟨1275363223891962007364897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3400968597045232019639725 1275363223891962007364897)
                      ·
                        rfl

theorem cell23_2483761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_2483761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483761 prefixEnd_2483761 := by exact prefixLift 2483761
  have htrace : WordTrace (prefixWord ++ tailWord_2483761) baseStart_2483761 baseEnd_2483761 := by
    simpa [prefixWord, tailWord_2483761, baseEnd_2483761] using wordTrace_append hprefix tailTrace_2483761
  have hstable : (prefixWord ++ tailWord_2483761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483761).length < 2 ^ (prefixWord ++ tailWord_2483761).sum := by decide
  have hdescent : baseEnd_2483761 < baseStart_2483761 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483801 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 3, 5, 2]
def baseStart_2483801 : Nat := 118140960795 + 2483801 * 2 ^ 59
def prefixEnd_2483801 : Nat := 4983230072969 + 3 ^ 40 * 2483801 * 2
def baseEnd_2483801 : Nat := 1275383763118141850864713

theorem tailTrace_2483801 : CollatzResearch.WordTrace tailWord_2483801 prefixEnd_2483801 1275383763118141850864713 := by
  unfold tailWord_2483801
  simp only [CollatzResearch.WordTrace]
  refine ⟨90591664874620651283667257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60394443249747100855778171 90591664874620651283667257)
  ·
    refine ⟨67943748655965488462750443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90591664874620651283667257 67943748655965488462750443)
    ·
      refine ⟨101915622983948232694125665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67943748655965488462750443 101915622983948232694125665)
      ·
        refine ⟨76436717237961174520594249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101915622983948232694125665 76436717237961174520594249)
        ·
          refine ⟨57327537928470880890445687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76436717237961174520594249 57327537928470880890445687)
          ·
            refine ⟨85991306892706321335668531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57327537928470880890445687 85991306892706321335668531)
            ·
              refine ⟨128986960339059482003502797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85991306892706321335668531 128986960339059482003502797)
              ·
                refine ⟨48370110127147305751313549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128986960339059482003502797 48370110127147305751313549)
                ·
                  refine ⟨18138791297680239656742581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48370110127147305751313549 18138791297680239656742581)
                  ·
                    refine ⟨1700511684157522467819617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18138791297680239656742581 1700511684157522467819617)
                    ·
                      refine ⟨1275383763118141850864713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700511684157522467819617 1275383763118141850864713)
                      ·
                        rfl

theorem cell23_2483801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 5, 2].length) (baseStart_2483801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483801 prefixEnd_2483801 := by exact prefixLift 2483801
  have htrace : WordTrace (prefixWord ++ tailWord_2483801) baseStart_2483801 baseEnd_2483801 := by
    simpa [prefixWord, tailWord_2483801, baseEnd_2483801] using wordTrace_append hprefix tailTrace_2483801
  have hstable : (prefixWord ++ tailWord_2483801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483801).length < 2 ^ (prefixWord ++ tailWord_2483801).sum := by decide
  have hdescent : baseEnd_2483801 < baseStart_2483801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483811 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 3, 5]
def baseStart_2483811 : Nat := 118140960795 + 2483811 * 2 ^ 59
def prefixEnd_2483811 : Nat := 4983230072969 + 3 ^ 40 * 2483811 * 2
def baseEnd_2483811 : Nat := 425129632641562270579889

theorem tailTrace_2483811 : CollatzResearch.WordTrace tailWord_2483811 prefixEnd_2483811 425129632641562270579889 := by
  unfold tailWord_2483811
  simp only [CollatzResearch.WordTrace]
  refine ⟨90592029604584422991531287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60394686403056281994354191 90592029604584422991531287)
  ·
    refine ⟨135888044406876634487296931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90592029604584422991531287 135888044406876634487296931)
    ·
      refine ⟨203832066610314951730945397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135888044406876634487296931 203832066610314951730945397)
      ·
        refine ⟨19109256244717026724776131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203832066610314951730945397 19109256244717026724776131)
        ·
          refine ⟨28663884367075540087164197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19109256244717026724776131 28663884367075540087164197)
          ·
            refine ⟨5374478318826663766343287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28663884367075540087164197 5374478318826663766343287)
            ·
              refine ⟨8061717478239995649514931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5374478318826663766343287 8061717478239995649514931)
              ·
                refine ⟨12092576217359993474272397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8061717478239995649514931 12092576217359993474272397)
                ·
                  refine ⟨4534716081509997552852149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12092576217359993474272397 4534716081509997552852149)
                  ·
                    refine ⟨425129632641562270579889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4534716081509997552852149 425129632641562270579889)
                    ·
                      rfl

theorem cell23_2483811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 5].length) (baseStart_2483811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483811 prefixEnd_2483811 := by exact prefixLift 2483811
  have htrace : WordTrace (prefixWord ++ tailWord_2483811) baseStart_2483811 baseEnd_2483811 := by
    simpa [prefixWord, tailWord_2483811, baseEnd_2483811] using wordTrace_append hprefix tailTrace_2483811
  have hstable : (prefixWord ++ tailWord_2483811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483811).length < 2 ^ (prefixWord ++ tailWord_2483811).sum := by decide
  have hdescent : baseEnd_2483811 < baseStart_2483811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483851 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 3]
def baseStart_2483851 : Nat := 118140960795 + 2483851 * 2 ^ 59
def prefixEnd_2483851 : Nat := 4983230072969 + 3 ^ 40 * 2483851 * 2
def baseEnd_2483851 : Nat := 1275409437150866655239483

theorem tailTrace_2483851 : CollatzResearch.WordTrace tailWord_2483851 prefixEnd_2483851 1275409437150866655239483 := by
  unfold tailWord_2483851
  simp only [CollatzResearch.WordTrace]
  refine ⟨90593488524439509822987407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60395659016293006548658271 90593488524439509822987407)
  ·
    refine ⟨135890232786659264734481111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90593488524439509822987407 135890232786659264734481111)
    ·
      refine ⟨203835349179988897101721667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135890232786659264734481111 203835349179988897101721667)
      ·
        refine ⟨305753023769983345652582501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203835349179988897101721667 305753023769983345652582501)
        ·
          refine ⟨57328691956871877309859219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 305753023769983345652582501 57328691956871877309859219)
          ·
            refine ⟨85993037935307815964788829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57328691956871877309859219 85993037935307815964788829)
            ·
              refine ⟨32247389225740430986795811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85993037935307815964788829 32247389225740430986795811)
              ·
                refine ⟨48371083838610646480193717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32247389225740430986795811 48371083838610646480193717)
                ·
                  refine ⟨4534789109869748107518161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48371083838610646480193717 4534789109869748107518161)
                  ·
                    refine ⟨3401091832402311080638621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4534789109869748107518161 3401091832402311080638621)
                    ·
                      refine ⟨1275409437150866655239483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3401091832402311080638621 1275409437150866655239483)
                      ·
                        rfl

theorem cell23_2483851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 2, 3].length) (baseStart_2483851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483851 prefixEnd_2483851 := by exact prefixLift 2483851
  have htrace : WordTrace (prefixWord ++ tailWord_2483851) baseStart_2483851 baseEnd_2483851 := by
    simpa [prefixWord, tailWord_2483851, baseEnd_2483851] using wordTrace_append hprefix tailTrace_2483851
  have hstable : (prefixWord ++ tailWord_2483851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483851).length < 2 ^ (prefixWord ++ tailWord_2483851).sum := by decide
  have hdescent : baseEnd_2483851 < baseStart_2483851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483885 : List Nat := [1, 5, 2, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_2483885 : Nat := 118140960795 + 2483885 * 2 ^ 59
def prefixEnd_2483885 : Nat := 4983230072969 + 3 ^ 40 * 2483885 * 2
def baseEnd_2483885 : Nat := 1275426895493119522214327

theorem tailTrace_2483885 : CollatzResearch.WordTrace tailWord_2483885 prefixEnd_2483885 1275426895493119522214327 := by
  unfold tailWord_2483885
  simp only [CollatzResearch.WordTrace]
  refine ⟨90594728606316333629725109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60396485737544222419816739 90594728606316333629725109)
  ·
    refine ⟨8493255806842156277786729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90594728606316333629725109 8493255806842156277786729)
    ·
      refine ⟨6369941855131617208340047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8493255806842156277786729 6369941855131617208340047)
      ·
        refine ⟨9554912782697425812510071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6369941855131617208340047 9554912782697425812510071)
        ·
          refine ⟨14332369174046138718765107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9554912782697425812510071 14332369174046138718765107)
          ·
            refine ⟨21498553761069208078147661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14332369174046138718765107 21498553761069208078147661)
            ·
              refine ⟨8061957660400953029305373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21498553761069208078147661 8061957660400953029305373)
              ·
                refine ⟨3023234122650357385989515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8061957660400953029305373 3023234122650357385989515)
                ·
                  refine ⟨4534851183975536078984273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023234122650357385989515 4534851183975536078984273)
                  ·
                    refine ⟨3401138387981652059238205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4534851183975536078984273 3401138387981652059238205)
                    ·
                      refine ⟨1275426895493119522214327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3401138387981652059238205 1275426895493119522214327)
                      ·
                        rfl

theorem cell23_2483885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_2483885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483885 prefixEnd_2483885 := by exact prefixLift 2483885
  have htrace : WordTrace (prefixWord ++ tailWord_2483885) baseStart_2483885 baseEnd_2483885 := by
    simpa [prefixWord, tailWord_2483885, baseEnd_2483885] using wordTrace_append hprefix tailTrace_2483885
  have hstable : (prefixWord ++ tailWord_2483885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483885).length < 2 ^ (prefixWord ++ tailWord_2483885).sum := by decide
  have hdescent : baseEnd_2483885 < baseStart_2483885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483933 : List Nat := [1, 4, 3, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_2483933 : Nat := 118140960795 + 2483933 * 2 ^ 59
def prefixEnd_2483933 : Nat := 4983230072969 + 3 ^ 40 * 2483933 * 2
def baseEnd_2483933 : Nat := 1275451542564535334414107

theorem tailTrace_2483933 : CollatzResearch.WordTrace tailWord_2483933 prefixEnd_2483933 1275451542564535334414107 := by
  unfold tailWord_2483933
  simp only [CollatzResearch.WordTrace]
  refine ⟨90596479310142437827472453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60397652873428291884981635 90596479310142437827472453)
  ·
    refine ⟨16986839870651707092651085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90596479310142437827472453 16986839870651707092651085)
    ·
      refine ⟨6370064951494390159744157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16986839870651707092651085 6370064951494390159744157)
      ·
        refine ⟨2388774356810396309904059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6370064951494390159744157 2388774356810396309904059)
        ·
          refine ⟨3583161535215594464856089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2388774356810396309904059 3583161535215594464856089)
          ·
            refine ⟨2687371151411695848642067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3583161535215594464856089 2687371151411695848642067)
            ·
              refine ⟨4031056727117543772963101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2687371151411695848642067 4031056727117543772963101)
              ·
                refine ⟨1511646272669078914861163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4031056727117543772963101 1511646272669078914861163)
                ·
                  refine ⟨2267469409003618372291745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511646272669078914861163 2267469409003618372291745)
                  ·
                    refine ⟨1700602056752713779218809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2267469409003618372291745 1700602056752713779218809)
                    ·
                      refine ⟨1275451542564535334414107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700602056752713779218809 1275451542564535334414107)
                      ·
                        rfl

theorem cell23_2483933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_2483933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483933 prefixEnd_2483933 := by exact prefixLift 2483933
  have htrace : WordTrace (prefixWord ++ tailWord_2483933) baseStart_2483933 baseEnd_2483933 := by
    simpa [prefixWord, tailWord_2483933, baseEnd_2483933] using wordTrace_append hprefix tailTrace_2483933
  have hstable : (prefixWord ++ tailWord_2483933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483933).length < 2 ^ (prefixWord ++ tailWord_2483933).sum := by decide
  have hdescent : baseEnd_2483933 < baseStart_2483933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483955 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 4, 2, 2]
def baseStart_2483955 : Nat := 118140960795 + 2483955 * 2 ^ 59
def prefixEnd_2483955 : Nat := 4983230072969 + 3 ^ 40 * 2483955 * 2
def baseEnd_2483955 : Nat := 1275462839138934248339005

theorem tailTrace_2483955 : CollatzResearch.WordTrace tailWord_2483955 prefixEnd_2483955 1275462839138934248339005 := by
  unfold tailWord_2483955
  simp only [CollatzResearch.WordTrace]
  refine ⟨90597281716062735584773319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60398187810708490389848879 90597281716062735584773319)
  ·
    refine ⟨135895922574094103377159979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90597281716062735584773319 135895922574094103377159979)
    ·
      refine ⟨203843883861141155065739969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135895922574094103377159979 203843883861141155065739969)
      ·
        refine ⟨152882912895855866299304977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203843883861141155065739969 152882912895855866299304977)
        ·
          refine ⟨114662184671891899724478733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152882912895855866299304977 114662184671891899724478733)
          ·
            refine ⟨42998319251959462396679525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114662184671891899724478733 42998319251959462396679525)
            ·
              refine ⟨8062184859742399199377411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42998319251959462396679525 8062184859742399199377411)
              ·
                refine ⟨12093277289613598799066117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8062184859742399199377411 12093277289613598799066117)
                ·
                  refine ⟨2267489491802549774824897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12093277289613598799066117 2267489491802549774824897)
                  ·
                    refine ⟨1700617118851912331118673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2267489491802549774824897 1700617118851912331118673)
                    ·
                      refine ⟨1275462839138934248339005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700617118851912331118673 1275462839138934248339005)
                      ·
                        rfl

theorem cell23_2483955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 2, 2].length) (baseStart_2483955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483955 prefixEnd_2483955 := by exact prefixLift 2483955
  have htrace : WordTrace (prefixWord ++ tailWord_2483955) baseStart_2483955 baseEnd_2483955 := by
    simpa [prefixWord, tailWord_2483955, baseEnd_2483955] using wordTrace_append hprefix tailTrace_2483955
  have hstable : (prefixWord ++ tailWord_2483955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483955).length < 2 ^ (prefixWord ++ tailWord_2483955).sum := by decide
  have hdescent : baseEnd_2483955 < baseStart_2483955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2483966 : List Nat := [4, 2, 2, 1, 3, 2, 2, 1, 2, 1, 3]
def baseStart_2483966 : Nat := 118140960795 + 2483966 * 2 ^ 59
def prefixEnd_2483966 : Nat := 4983230072969 + 3 ^ 40 * 2483966 * 2
def baseEnd_2483966 : Nat := 1275468487426133705301455

theorem tailTrace_2483966 : CollatzResearch.WordTrace tailWord_2483966 prefixEnd_2483966 1275468487426133705301455 := by
  unfold tailWord_2483966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11324710364877860557927969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60398455279348589642282501 11324710364877860557927969)
  ·
    refine ⟨8493532773658395418445977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11324710364877860557927969 8493532773658395418445977)
    ·
      refine ⟨6370149580243796563834483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8493532773658395418445977 6370149580243796563834483)
      ·
        refine ⟨9555224370365694845751725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6370149580243796563834483 9555224370365694845751725)
        ·
          refine ⟨3583209138887135567156897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9555224370365694845751725 3583209138887135567156897)
          ·
            refine ⟨2687406854165351675367673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3583209138887135567156897 2687406854165351675367673)
            ·
              refine ⟨2015555140624013756525755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2687406854165351675367673 2015555140624013756525755)
              ·
                refine ⟨3023332710936020634788633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015555140624013756525755 3023332710936020634788633)
                ·
                  refine ⟨2267499533202015476091475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3023332710936020634788633 2267499533202015476091475)
                  ·
                    refine ⟨3401249299803023214137213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2267499533202015476091475 3401249299803023214137213)
                    ·
                      refine ⟨1275468487426133705301455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3401249299803023214137213 1275468487426133705301455)
                      ·
                        rfl

theorem cell23_2483966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 2, 1, 3].length) (baseStart_2483966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2483966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2483966 prefixEnd_2483966 := by exact prefixLift 2483966
  have htrace : WordTrace (prefixWord ++ tailWord_2483966) baseStart_2483966 baseEnd_2483966 := by
    simpa [prefixWord, tailWord_2483966, baseEnd_2483966] using wordTrace_append hprefix tailTrace_2483966
  have hstable : (prefixWord ++ tailWord_2483966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2483966).length < 2 ^ (prefixWord ++ tailWord_2483966).sum := by decide
  have hdescent : baseEnd_2483966 < baseStart_2483966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2483966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484012 : List Nat := [2, 2, 1, 1, 1, 7, 2, 2, 5]
def baseStart_2484012 : Nat := 118140960795 + 2484012 * 2 ^ 59
def prefixEnd_2484012 : Nat := 4983230072969 + 3 ^ 40 * 2484012 * 2
def baseEnd_2484012 : Nat := 141721345281804502814027

theorem tailTrace_2484012 : CollatzResearch.WordTrace tailWord_2484012 prefixEnd_2484012 141721345281804502814027 := by
  unfold tailWord_2484012
  simp only [CollatzResearch.WordTrace]
  refine ⟨45299680338428117159799145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60399573784570822879732193 45299680338428117159799145)
  ·
    refine ⟨33974760253821087869849359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45299680338428117159799145 33974760253821087869849359)
    ·
      refine ⟨50962140380731631804774039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33974760253821087869849359 50962140380731631804774039)
      ·
        refine ⟨76443210571097447707161059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50962140380731631804774039 76443210571097447707161059)
        ·
          refine ⟨114664815856646171560741589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76443210571097447707161059 114664815856646171560741589)
          ·
            refine ⟨2687456621640144645954881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 114664815856646171560741589 2687456621640144645954881)
            ·
              refine ⟨2015592466230108484466161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2687456621640144645954881 2015592466230108484466161)
              ·
                refine ⟨1511694349672581363349621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2015592466230108484466161 1511694349672581363349621)
                ·
                  refine ⟨141721345281804502814027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1511694349672581363349621 141721345281804502814027)
                  ·
                    rfl

theorem cell23_2484012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 5].length) (baseStart_2484012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484012 prefixEnd_2484012 := by exact prefixLift 2484012
  have htrace : WordTrace (prefixWord ++ tailWord_2484012) baseStart_2484012 baseEnd_2484012 := by
    simpa [prefixWord, tailWord_2484012, baseEnd_2484012] using wordTrace_append hprefix tailTrace_2484012
  have hstable : (prefixWord ++ tailWord_2484012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484012).length < 2 ^ (prefixWord ++ tailWord_2484012).sum := by decide
  have hdescent : baseEnd_2484012 < baseStart_2484012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484018 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5]
def baseStart_2484018 : Nat := 118140960795 + 2484018 * 2 ^ 59
def prefixEnd_2484018 : Nat := 4983230072969 + 3 ^ 40 * 2484018 * 2
def baseEnd_2484018 : Nat := 1275495188420167501851215

theorem tailTrace_2484018 : CollatzResearch.WordTrace tailWord_2484018 prefixEnd_2484018 1275495188420167501851215 := by
  unfold tailWord_2484018
  simp only [CollatzResearch.WordTrace]
  refine ⟨22649894878708624336079177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60399719676556331562877805 22649894878708624336079177)
  ·
    refine ⟨16987421159031468252059383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22649894878708624336079177 16987421159031468252059383)
    ·
      refine ⟨25481131738547202378089075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16987421159031468252059383 25481131738547202378089075)
      ·
        refine ⟨38221697607820803567133613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25481131738547202378089075 38221697607820803567133613)
        ·
          refine ⟨14333136602932801337675105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38221697607820803567133613 14333136602932801337675105)
          ·
            refine ⟨10749852452199601003256329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14333136602932801337675105 10749852452199601003256329)
            ·
              refine ⟨8062389339149700752442247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10749852452199601003256329 8062389339149700752442247)
              ·
                refine ⟨12093584008724551128663371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8062389339149700752442247 12093584008724551128663371)
                ·
                  refine ⟨18140376013086826692995057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12093584008724551128663371 18140376013086826692995057)
                  ·
                    refine ⟨13605282009815120019746293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18140376013086826692995057 13605282009815120019746293)
                    ·
                      refine ⟨1275495188420167501851215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13605282009815120019746293 1275495188420167501851215)
                      ·
                        rfl

theorem cell23_2484018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_2484018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484018 prefixEnd_2484018 := by exact prefixLift 2484018
  have htrace : WordTrace (prefixWord ++ tailWord_2484018) baseStart_2484018 baseEnd_2484018 := by
    simpa [prefixWord, tailWord_2484018, baseEnd_2484018] using wordTrace_append hprefix tailTrace_2484018
  have hstable : (prefixWord ++ tailWord_2484018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484018).length < 2 ^ (prefixWord ++ tailWord_2484018).sum := by decide
  have hdescent : baseEnd_2484018 < baseStart_2484018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484022 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2484022 : Nat := 118140960795 + 2484022 * 2 ^ 59
def prefixEnd_2484022 : Nat := 4983230072969 + 3 ^ 40 * 2484022 * 2
def baseEnd_2484022 : Nat := 1275497242342785486201197

theorem tailTrace_2484022 : CollatzResearch.WordTrace tailWord_2484022 prefixEnd_2484022 1275497242342785486201197 := by
  unfold tailWord_2484022
  simp only [CollatzResearch.WordTrace]
  refine ⟨5662482837926250376716395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60399816937880004018308213 5662482837926250376716395)
  ·
    refine ⟨8493724256889375565074593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5662482837926250376716395 8493724256889375565074593)
    ·
      refine ⟨6370293192667031673805945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8493724256889375565074593 6370293192667031673805945)
      ·
        refine ⟨4777719894500273755354459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6370293192667031673805945 4777719894500273755354459)
        ·
          refine ⟨7166579841750410633031689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4777719894500273755354459 7166579841750410633031689)
          ·
            refine ⟨5374934881312807974773767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7166579841750410633031689 5374934881312807974773767)
            ·
              refine ⟨8062402321969211962160651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5374934881312807974773767 8062402321969211962160651)
              ·
                refine ⟨12093603482953817943240977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8062402321969211962160651 12093603482953817943240977)
                ·
                  refine ⟨9070202612215363457430733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12093603482953817943240977 9070202612215363457430733)
                  ·
                    refine ⟨3401325979580761296536525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9070202612215363457430733 3401325979580761296536525)
                    ·
                      refine ⟨1275497242342785486201197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3401325979580761296536525 1275497242342785486201197)
                      ·
                        rfl

theorem cell23_2484022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2484022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484022 prefixEnd_2484022 := by exact prefixLift 2484022
  have htrace : WordTrace (prefixWord ++ tailWord_2484022) baseStart_2484022 baseEnd_2484022 := by
    simpa [prefixWord, tailWord_2484022, baseEnd_2484022] using wordTrace_append hprefix tailTrace_2484022
  have hstable : (prefixWord ++ tailWord_2484022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484022).length < 2 ^ (prefixWord ++ tailWord_2484022).sum := by decide
  have hdescent : baseEnd_2484022 < baseStart_2484022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484028 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_2484028 : Nat := 118140960795 + 2484028 * 2 ^ 59
def prefixEnd_2484028 : Nat := 4983230072969 + 3 ^ 40 * 2484028 * 2
def baseEnd_2484028 : Nat := 1275500323226712462726169

theorem tailTrace_2484028 : CollatzResearch.WordTrace tailWord_2484028 prefixEnd_2484028 1275500323226712462726169 := by
  unfold tailWord_2484028
  simp only [CollatzResearch.WordTrace]
  refine ⟨45299972122399134526090369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60399962829865512701453825 45299972122399134526090369)
  ·
    refine ⟨33974979091799350894567777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45299972122399134526090369 33974979091799350894567777)
    ·
      refine ⟨25481234318849513170925833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33974979091799350894567777 25481234318849513170925833)
      ·
        refine ⟨19110925739137134878194375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25481234318849513170925833 19110925739137134878194375)
        ·
          refine ⟨28666388608705702317291563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19110925739137134878194375 28666388608705702317291563)
          ·
            refine ⟨42999582913058553475937345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28666388608705702317291563 42999582913058553475937345)
            ·
              refine ⟨32249687184793915106953009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42999582913058553475937345 32249687184793915106953009)
              ·
                refine ⟨24187265388595436330214757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32249687184793915106953009 24187265388595436330214757)
                ·
                  refine ⟨4535112260361644311915267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24187265388595436330214757 4535112260361644311915267)
                  ·
                    refine ⟨6802668390542466467872901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4535112260361644311915267 6802668390542466467872901)
                    ·
                      refine ⟨1275500323226712462726169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6802668390542466467872901 1275500323226712462726169)
                      ·
                        rfl

theorem cell23_2484028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_2484028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484028 prefixEnd_2484028 := by exact prefixLift 2484028
  have htrace : WordTrace (prefixWord ++ tailWord_2484028) baseStart_2484028 baseEnd_2484028 := by
    simpa [prefixWord, tailWord_2484028, baseEnd_2484028] using wordTrace_append hprefix tailTrace_2484028
  have hstable : (prefixWord ++ tailWord_2484028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484028).length < 2 ^ (prefixWord ++ tailWord_2484028).sum := by decide
  have hdescent : baseEnd_2484028 < baseStart_2484028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484072 : List Nat := [2, 1, 4, 2, 1, 1, 1, 6, 1, 4]
def baseStart_2484072 : Nat := 118140960795 + 2484072 * 2 ^ 59
def prefixEnd_2484072 : Nat := 4983230072969 + 3 ^ 40 * 2484072 * 2
def baseEnd_2484072 : Nat := 425174305458503430191989

theorem tailTrace_2484072 : CollatzResearch.WordTrace tailWord_2484072 prefixEnd_2484072 425174305458503430191989 := by
  unfold tailWord_2484072
  simp only [CollatzResearch.WordTrace]
  refine ⟨45300774528319432283391235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60401032704425909711188313 45300774528319432283391235)
  ·
    refine ⟨67951161792479148425086853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45300774528319432283391235 67951161792479148425086853)
    ·
      refine ⟨12740842836089840329703785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67951161792479148425086853 12740842836089840329703785)
      ·
        refine ⟨9555632127067380247277839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12740842836089840329703785 9555632127067380247277839)
        ·
          refine ⟨14333448190601070370916759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9555632127067380247277839 14333448190601070370916759)
          ·
            refine ⟨21500172285901605556375139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14333448190601070370916759 21500172285901605556375139)
            ·
              refine ⟨32250258428852408334562709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21500172285901605556375139 32250258428852408334562709)
              ·
                refine ⟨1511730863852456640682627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32250258428852408334562709 1511730863852456640682627)
                ·
                  refine ⟨2267596295778684961023941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511730863852456640682627 2267596295778684961023941)
                  ·
                    refine ⟨425174305458503430191989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2267596295778684961023941 425174305458503430191989)
                    ·
                      rfl

theorem cell23_2484072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_2484072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484072 prefixEnd_2484072 := by exact prefixLift 2484072
  have htrace : WordTrace (prefixWord ++ tailWord_2484072) baseStart_2484072 baseEnd_2484072 := by
    simpa [prefixWord, tailWord_2484072, baseEnd_2484072] using wordTrace_append hprefix tailTrace_2484072
  have hstable : (prefixWord ++ tailWord_2484072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484072).length < 2 ^ (prefixWord ++ tailWord_2484072).sum := by decide
  have hdescent : baseEnd_2484072 < baseStart_2484072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484105 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 1, 5, 2]
def baseStart_2484105 : Nat := 118140960795 + 2484105 * 2 ^ 59
def prefixEnd_2484105 : Nat := 4983230072969 + 3 ^ 40 * 2484105 * 2
def baseEnd_2484105 : Nat := 1275539861237108661463315

theorem tailTrace_2484105 : CollatzResearch.WordTrace tailWord_2484105 prefixEnd_2484105 1275539861237108661463315 := by
  unfold tailWord_2484105
  simp only [CollatzResearch.WordTrace]
  refine ⟨90602752665519311202733769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60401835110346207468489179 90602752665519311202733769)
  ·
    refine ⟨67952064499139483402050327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90602752665519311202733769 67952064499139483402050327)
    ·
      refine ⟨101928096748709225103075491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67952064499139483402050327 101928096748709225103075491)
      ·
        refine ⟨152892145123063837654613237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101928096748709225103075491 152892145123063837654613237)
        ·
          refine ⟨14333638605287234780119991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152892145123063837654613237 14333638605287234780119991)
          ·
            refine ⟨21500457907930852170179987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14333638605287234780119991 21500457907930852170179987)
            ·
              refine ⟨32250686861896278255269981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21500457907930852170179987 32250686861896278255269981)
              ·
                refine ⟨12094007573211104345726243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32250686861896278255269981 12094007573211104345726243)
                ·
                  refine ⟨18141011359816656518589365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12094007573211104345726243 18141011359816656518589365)
                  ·
                    refine ⟨1700719814982811548617753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18141011359816656518589365 1700719814982811548617753)
                    ·
                      refine ⟨1275539861237108661463315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700719814982811548617753 1275539861237108661463315)
                      ·
                        rfl

theorem cell23_2484105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 5, 2].length) (baseStart_2484105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484105 prefixEnd_2484105 := by exact prefixLift 2484105
  have htrace : WordTrace (prefixWord ++ tailWord_2484105) baseStart_2484105 baseEnd_2484105 := by
    simpa [prefixWord, tailWord_2484105, baseEnd_2484105] using wordTrace_append hprefix tailTrace_2484105
  have hstable : (prefixWord ++ tailWord_2484105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484105).length < 2 ^ (prefixWord ++ tailWord_2484105).sum := by decide
  have hdescent : baseEnd_2484105 < baseStart_2484105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484106 : List Nat := [3, 1, 2, 4, 2, 2, 1, 3, 1, 4]
def baseStart_2484106 : Nat := 118140960795 + 2484106 * 2 ^ 59
def prefixEnd_2484106 : Nat := 4983230072969 + 3 ^ 40 * 2484106 * 2
def baseEnd_2484106 : Nat := 425180124905921052516937

theorem tailTrace_2484106 : CollatzResearch.WordTrace tailWord_2484106 prefixEnd_2484106 425180124905921052516937 := by
  unfold tailWord_2484106
  simp only [CollatzResearch.WordTrace]
  refine ⟨22650697284628922093380043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60401859425677125582346781 22650697284628922093380043)
  ·
    refine ⟨33976045926943383140070065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22650697284628922093380043 33976045926943383140070065)
    ·
      refine ⟨25482034445207537355052549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33976045926943383140070065 25482034445207537355052549)
      ·
        refine ⟨4777881458476413254072353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25482034445207537355052549 4777881458476413254072353)
        ·
          refine ⟨3583411093857309940554265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4777881458476413254072353 3583411093857309940554265)
          ·
            refine ⟨2687558320392982455415699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3583411093857309940554265 2687558320392982455415699)
            ·
              refine ⟨4031337480589473683123549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2687558320392982455415699 4031337480589473683123549)
              ·
                refine ⟨1511751555221052631171331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4031337480589473683123549 1511751555221052631171331)
                ·
                  refine ⟨2267627332831578946756997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1511751555221052631171331 2267627332831578946756997)
                  ·
                    refine ⟨425180124905921052516937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2267627332831578946756997 425180124905921052516937)
                    ·
                      rfl

theorem cell23_2484106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_2484106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484106 prefixEnd_2484106 := by exact prefixLift 2484106
  have htrace : WordTrace (prefixWord ++ tailWord_2484106) baseStart_2484106 baseEnd_2484106 := by
    simpa [prefixWord, tailWord_2484106, baseEnd_2484106] using wordTrace_append hprefix tailTrace_2484106
  have hstable : (prefixWord ++ tailWord_2484106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484106).length < 2 ^ (prefixWord ++ tailWord_2484106).sum := by decide
  have hdescent : baseEnd_2484106 < baseStart_2484106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484122 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2]
def baseStart_2484122 : Nat := 118140960795 + 2484122 * 2 ^ 59
def prefixEnd_2484122 : Nat := 4983230072969 + 3 ^ 40 * 2484122 * 2
def baseEnd_2484122 : Nat := 1275548590408235094950737

theorem tailTrace_2484122 : CollatzResearch.WordTrace tailWord_2484122 prefixEnd_2484122 1275548590408235094950737 := by
  unfold tailWord_2484122
  simp only [CollatzResearch.WordTrace]
  refine ⟨22650843176614430776525655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60402248470971815404068413 22650843176614430776525655)
  ·
    refine ⟨33976264764921646164788483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22650843176614430776525655 33976264764921646164788483)
    ·
      refine ⟨50964397147382469247182725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33976264764921646164788483 50964397147382469247182725)
      ·
        refine ⟨9555824465134212983846761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50964397147382469247182725 9555824465134212983846761)
        ·
          refine ⟨7166868348850659737885071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9555824465134212983846761 7166868348850659737885071)
          ·
            refine ⟨10750302523275989606827607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7166868348850659737885071 10750302523275989606827607)
            ·
              refine ⟨16125453784913984410241411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10750302523275989606827607 16125453784913984410241411)
              ·
                refine ⟨24188180677370976615362117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16125453784913984410241411 24188180677370976615362117)
                ·
                  refine ⟨4535283877007058115380397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24188180677370976615362117 4535283877007058115380397)
                  ·
                    refine ⟨1700731453877646793267649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4535283877007058115380397 1700731453877646793267649)
                    ·
                      refine ⟨1275548590408235094950737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700731453877646793267649 1275548590408235094950737)
                      ·
                        rfl

theorem cell23_2484122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_2484122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484122 prefixEnd_2484122 := by exact prefixLift 2484122
  have htrace : WordTrace (prefixWord ++ tailWord_2484122) baseStart_2484122 baseEnd_2484122 := by
    simpa [prefixWord, tailWord_2484122, baseEnd_2484122] using wordTrace_append hprefix tailTrace_2484122
  have hstable : (prefixWord ++ tailWord_2484122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484122).length < 2 ^ (prefixWord ++ tailWord_2484122).sum := by decide
  have hdescent : baseEnd_2484122 < baseStart_2484122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484136 : List Nat := [2, 1, 6, 2, 1, 2, 2, 1, 6]
def baseStart_2484136 : Nat := 118140960795 + 2484136 * 2 ^ 59
def prefixEnd_2484136 : Nat := 4983230072969 + 3 ^ 40 * 2484136 * 2
def baseEnd_2484136 : Nat := 141728419904155337797297

theorem tailTrace_2484136 : CollatzResearch.WordTrace tailWord_2484136 prefixEnd_2484136 141728419904155337797297 := by
  unfold tailWord_2484136
  simp only [CollatzResearch.WordTrace]
  refine ⟨45301941664203501748556131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60402588885604668998074841 45301941664203501748556131)
  ·
    refine ⟨67952912496305252622834197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45301941664203501748556131 67952912496305252622834197)
    ·
      refine ⟨3185292773264308716695353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67952912496305252622834197 3185292773264308716695353)
      ·
        refine ⟨2388969579948231537521515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3185292773264308716695353 2388969579948231537521515)
        ·
          refine ⟨3583454369922347306282273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2388969579948231537521515 3583454369922347306282273)
          ·
            refine ⟨2687590777441760479711705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3583454369922347306282273 2687590777441760479711705)
            ·
              refine ⟨2015693083081320359783779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2687590777441760479711705 2015693083081320359783779)
              ·
                refine ⟨3023539624621980539675669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2015693083081320359783779 3023539624621980539675669)
                ·
                  refine ⟨141728419904155337797297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3023539624621980539675669 141728419904155337797297)
                  ·
                    rfl

theorem cell23_2484136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 6].length) (baseStart_2484136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484136 prefixEnd_2484136 := by exact prefixLift 2484136
  have htrace : WordTrace (prefixWord ++ tailWord_2484136) baseStart_2484136 baseEnd_2484136 := by
    simpa [prefixWord, tailWord_2484136, baseEnd_2484136] using wordTrace_append hprefix tailTrace_2484136
  have hstable : (prefixWord ++ tailWord_2484136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484136).length < 2 ^ (prefixWord ++ tailWord_2484136).sum := by decide
  have hdescent : baseEnd_2484136 < baseStart_2484136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484152 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 5, 2, 2]
def baseStart_2484152 : Nat := 118140960795 + 2484152 * 2 ^ 59
def prefixEnd_2484152 : Nat := 4983230072969 + 3 ^ 40 * 2484152 * 2
def baseEnd_2484152 : Nat := 1275563994827869977575599

theorem tailTrace_2484152 : CollatzResearch.WordTrace tailWord_2484152 prefixEnd_2484152 1275563994827869977575599 := by
  unfold tailWord_2484152
  simp only [CollatzResearch.WordTrace]
  refine ⟨45302233448174519114847355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60402977930899358819796473 45302233448174519114847355)
  ·
    refine ⟨67953350172261778672271033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45302233448174519114847355 67953350172261778672271033)
    ·
      refine ⟨50965012629196334004203275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67953350172261778672271033 50965012629196334004203275)
      ·
        refine ⟨76447518943794501006304913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50965012629196334004203275 76447518943794501006304913)
        ·
          refine ⟨57335639207845875754728685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76447518943794501006304913 57335639207845875754728685)
          ·
            refine ⟨21500864702942203408023257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57335639207845875754728685 21500864702942203408023257)
            ·
              refine ⟨16125648527206652556017443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21500864702942203408023257 16125648527206652556017443)
              ·
                refine ⟨24188472790809978834026165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16125648527206652556017443 24188472790809978834026165)
                ·
                  refine ⟨2267669324138435515689953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24188472790809978834026165 2267669324138435515689953)
                  ·
                    refine ⟨1700751993103826636767465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2267669324138435515689953 1700751993103826636767465)
                    ·
                      refine ⟨1275563994827869977575599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700751993103826636767465 1275563994827869977575599)
                      ·
                        rfl

theorem cell23_2484152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 5, 2, 2].length) (baseStart_2484152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484152 prefixEnd_2484152 := by exact prefixLift 2484152
  have htrace : WordTrace (prefixWord ++ tailWord_2484152) baseStart_2484152 baseEnd_2484152 := by
    simpa [prefixWord, tailWord_2484152, baseEnd_2484152] using wordTrace_append hprefix tailTrace_2484152
  have hstable : (prefixWord ++ tailWord_2484152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484152).length < 2 ^ (prefixWord ++ tailWord_2484152).sum := by decide
  have hdescent : baseEnd_2484152 < baseStart_2484152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484156 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 2, 3, 2]
def baseStart_2484156 : Nat := 118140960795 + 2484156 * 2 ^ 59
def prefixEnd_2484156 : Nat := 4983230072969 + 3 ^ 40 * 2484156 * 2
def baseEnd_2484156 : Nat := 1275566048750487961925581

theorem tailTrace_2484156 : CollatzResearch.WordTrace tailWord_2484156 prefixEnd_2484156 1275566048750487961925581 := by
  unfold tailWord_2484156
  simp only [CollatzResearch.WordTrace]
  refine ⟨45302306394167273456420161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60403075192223031275226881 45302306394167273456420161)
  ·
    refine ⟨33976729795625455092315121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45302306394167273456420161 33976729795625455092315121)
    ·
      refine ⟨25482547346719091319236341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33976729795625455092315121 25482547346719091319236341)
      ·
        refine ⟨2388988813754914811178407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25482547346719091319236341 2388988813754914811178407)
        ·
          refine ⟨3583483220632372216767611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2388988813754914811178407 3583483220632372216767611)
          ·
            refine ⟨5375224830948558325151417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3583483220632372216767611 5375224830948558325151417)
            ·
              refine ⟨4031418623211418743863563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5375224830948558325151417 4031418623211418743863563)
              ·
                refine ⟨6047127934817128115795345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4031418623211418743863563 6047127934817128115795345)
                ·
                  refine ⟨4535345951112846086846509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6047127934817128115795345 4535345951112846086846509)
                  ·
                    refine ⟨1700754731667317282567441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4535345951112846086846509 1700754731667317282567441)
                    ·
                      refine ⟨1275566048750487961925581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700754731667317282567441 1275566048750487961925581)
                      ·
                        rfl

theorem cell23_2484156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_2484156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484156 prefixEnd_2484156 := by exact prefixLift 2484156
  have htrace : WordTrace (prefixWord ++ tailWord_2484156) baseStart_2484156 baseEnd_2484156 := by
    simpa [prefixWord, tailWord_2484156, baseEnd_2484156] using wordTrace_append hprefix tailTrace_2484156
  have hstable : (prefixWord ++ tailWord_2484156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484156).length < 2 ^ (prefixWord ++ tailWord_2484156).sum := by decide
  have hdescent : baseEnd_2484156 < baseStart_2484156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484172 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 1, 1, 5]
def baseStart_2484172 : Nat := 118140960795 + 2484172 * 2 ^ 59
def prefixEnd_2484172 : Nat := 4983230072969 + 3 ^ 40 * 2484172 * 2
def baseEnd_2484172 : Nat := 1275574264440959899325507

theorem tailTrace_2484172 : CollatzResearch.WordTrace tailWord_2484172 prefixEnd_2484172 1275574264440959899325507 := by
  unfold tailWord_2484172
  simp only [CollatzResearch.WordTrace]
  refine ⟨45302598178138290822711385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60403464237517721096948513 45302598178138290822711385)
  ·
    refine ⟨33976948633603718117033539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45302598178138290822711385 33976948633603718117033539)
    ·
      refine ⟨50965422950405577175550309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33976948633603718117033539 50965422950405577175550309)
      ·
        refine ⟨9556016803201045720415683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50965422950405577175550309 9556016803201045720415683)
        ·
          refine ⟨14334025204801568580623525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9556016803201045720415683 14334025204801568580623525)
          ·
            refine ⟨2687629725900294108866911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14334025204801568580623525 2687629725900294108866911)
            ·
              refine ⟨4031444588850441163300367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2687629725900294108866911 4031444588850441163300367)
              ·
                refine ⟨6047166883275661744950551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4031444588850441163300367 6047166883275661744950551)
                ·
                  refine ⟨9070750324913492617425827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6047166883275661744950551 9070750324913492617425827)
                  ·
                    refine ⟨13606125487370238926138741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9070750324913492617425827 13606125487370238926138741)
                    ·
                      refine ⟨1275574264440959899325507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13606125487370238926138741 1275574264440959899325507)
                      ·
                        rfl

theorem cell23_2484172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_2484172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484172 prefixEnd_2484172 := by exact prefixLift 2484172
  have htrace : WordTrace (prefixWord ++ tailWord_2484172) baseStart_2484172 baseEnd_2484172 := by
    simpa [prefixWord, tailWord_2484172, baseEnd_2484172] using wordTrace_append hprefix tailTrace_2484172
  have hstable : (prefixWord ++ tailWord_2484172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484172).length < 2 ^ (prefixWord ++ tailWord_2484172).sum := by decide
  have hdescent : baseEnd_2484172 < baseStart_2484172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484202 : List Nat := [3, 1, 3, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_2484202 : Nat := 118140960795 + 2484202 * 2 ^ 59
def prefixEnd_2484202 : Nat := 4983230072969 + 3 ^ 40 * 2484202 * 2
def baseEnd_2484202 : Nat := 1275589668860594781950369

theorem tailTrace_2484202 : CollatzResearch.WordTrace tailWord_2484202 prefixEnd_2484202 1275589668860594781950369 := by
  unfold tailWord_2484202
  simp only [CollatzResearch.WordTrace]
  refine ⟨22651572636541974192253715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60404193697445264512676573 22651572636541974192253715)
  ·
    refine ⟨33977358954812961288380573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22651572636541974192253715 33977358954812961288380573)
    ·
      refine ⟨12741509608054860483142715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33977358954812961288380573 12741509608054860483142715)
      ·
        refine ⟨19112264412082290724714073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12741509608054860483142715 19112264412082290724714073)
        ·
          refine ⟨14334198309061718043535555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19112264412082290724714073 14334198309061718043535555)
          ·
            refine ⟨21501297463592577065303333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14334198309061718043535555 21501297463592577065303333)
            ·
              refine ⟨4031493274423608199744375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21501297463592577065303333 4031493274423608199744375)
              ·
                refine ⟨6047239911635412299616563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4031493274423608199744375 6047239911635412299616563)
                ·
                  refine ⟨9070859867453118449424845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6047239911635412299616563 9070859867453118449424845)
                  ·
                    refine ⟨3401572450294919418534317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9070859867453118449424845 3401572450294919418534317)
                    ·
                      refine ⟨1275589668860594781950369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3401572450294919418534317 1275589668860594781950369)
                      ·
                        rfl

theorem cell23_2484202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_2484202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484202 prefixEnd_2484202 := by exact prefixLift 2484202
  have htrace : WordTrace (prefixWord ++ tailWord_2484202) baseStart_2484202 baseEnd_2484202 := by
    simpa [prefixWord, tailWord_2484202, baseEnd_2484202] using wordTrace_append hprefix tailTrace_2484202
  have hstable : (prefixWord ++ tailWord_2484202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484202).length < 2 ^ (prefixWord ++ tailWord_2484202).sum := by decide
  have hdescent : baseEnd_2484202 < baseStart_2484202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484229 : List Nat := [1, 3, 1, 1, 2, 5, 1, 3, 1, 3, 2]
def baseStart_2484229 : Nat := 118140960795 + 2484229 * 2 ^ 59
def prefixEnd_2484229 : Nat := 4983230072969 + 3 ^ 40 * 2484229 * 2
def baseEnd_2484229 : Nat := 1275603532838266176312745

theorem tailTrace_2484229 : CollatzResearch.WordTrace tailWord_2484229 prefixEnd_2484229 1275603532838266176312745 := by
  unfold tailWord_2484229
  simp only [CollatzResearch.WordTrace]
  refine ⟨90607275317070080380247741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60404850211380053586831827 90607275317070080380247741)
  ·
    refine ⟨33977728243901280142592903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90607275317070080380247741 33977728243901280142592903)
    ·
      refine ⟨50966592365851920213889355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33977728243901280142592903 50966592365851920213889355)
      ·
        refine ⟨76449888548777880320834033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50966592365851920213889355 76449888548777880320834033)
        ·
          refine ⟨57337416411583410240625525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76449888548777880320834033 57337416411583410240625525)
          ·
            refine ⟨5375382788585944710058643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57337416411583410240625525 5375382788585944710058643)
            ·
              refine ⟨8063074182878917065087965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5375382788585944710058643 8063074182878917065087965)
              ·
                refine ⟨3023652818579593899407987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8063074182878917065087965 3023652818579593899407987)
                ·
                  refine ⟨4535479227869390849111981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023652818579593899407987 4535479227869390849111981)
                  ·
                    refine ⟨1700804710451021568416993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4535479227869390849111981 1700804710451021568416993)
                    ·
                      refine ⟨1275603532838266176312745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700804710451021568416993 1275603532838266176312745)
                      ·
                        rfl

theorem cell23_2484229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 3, 2].length) (baseStart_2484229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484229 prefixEnd_2484229 := by exact prefixLift 2484229
  have htrace : WordTrace (prefixWord ++ tailWord_2484229) baseStart_2484229 baseEnd_2484229 := by
    simpa [prefixWord, tailWord_2484229, baseEnd_2484229] using wordTrace_append hprefix tailTrace_2484229
  have hstable : (prefixWord ++ tailWord_2484229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484229).length < 2 ^ (prefixWord ++ tailWord_2484229).sum := by decide
  have hdescent : baseEnd_2484229 < baseStart_2484229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484255 : List Nat := [1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 4]
def baseStart_2484255 : Nat := 118140960795 + 2484255 * 2 ^ 59
def prefixEnd_2484255 : Nat := 4983230072969 + 3 ^ 40 * 2484255 * 2
def baseEnd_2484255 : Nat := 1275616883335283074587625

theorem tailTrace_2484255 : CollatzResearch.WordTrace tailWord_2484255 prefixEnd_2484255 1275616883335283074587625 := by
  unfold tailWord_2484255
  simp only [CollatzResearch.WordTrace]
  refine ⟨90608223614975886820694219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60405482409983924547129479 90608223614975886820694219)
  ·
    refine ⟨135912335422463830231041329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90608223614975886820694219 135912335422463830231041329)
    ·
      refine ⟨101934251566847872673280997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135912335422463830231041329 101934251566847872673280997)
      ·
        refine ⟨19112672168783976126240187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101934251566847872673280997 19112672168783976126240187)
        ·
          refine ⟨28669008253175964189360281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19112672168783976126240187 28669008253175964189360281)
          ·
            refine ⟨21501756189881973142020211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28669008253175964189360281 21501756189881973142020211)
            ·
              refine ⟨32252634284822959713030317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21501756189881973142020211 32252634284822959713030317)
              ·
                refine ⟨12094737856808609892386369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32252634284822959713030317 12094737856808609892386369)
                ·
                  refine ⟨9071053392606457419289777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12094737856808609892386369 9071053392606457419289777)
                  ·
                    refine ⟨6803290044454843064467333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9071053392606457419289777 6803290044454843064467333)
                    ·
                      refine ⟨1275616883335283074587625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6803290044454843064467333 1275616883335283074587625)
                      ·
                        rfl

theorem cell23_2484255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_2484255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484255 prefixEnd_2484255 := by exact prefixLift 2484255
  have htrace : WordTrace (prefixWord ++ tailWord_2484255) baseStart_2484255 baseEnd_2484255 := by
    simpa [prefixWord, tailWord_2484255, baseEnd_2484255] using wordTrace_append hprefix tailTrace_2484255
  have hstable : (prefixWord ++ tailWord_2484255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484255).length < 2 ^ (prefixWord ++ tailWord_2484255).sum := by decide
  have hdescent : baseEnd_2484255 < baseStart_2484255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484263 : List Nat := [1, 1, 7, 1, 2, 1, 2, 2, 1, 3, 2]
def baseStart_2484263 : Nat := 118140960795 + 2484263 * 2 ^ 59
def prefixEnd_2484263 : Nat := 4983230072969 + 3 ^ 40 * 2484263 * 2
def baseEnd_2484263 : Nat := 1275620991180519043287589

theorem tailTrace_2484263 : CollatzResearch.WordTrace tailWord_2484263 prefixEnd_2484263 1275620991180519043287589 := by
  unfold tailWord_2484263
  simp only [CollatzResearch.WordTrace]
  refine ⟨90608515398946904186985443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60405676932631269457990295 90608515398946904186985443)
  ·
    refine ⟨135912773098420356280478165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90608515398946904186985443 135912773098420356280478165)
    ·
      refine ⟨3185455619494227100323707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 135912773098420356280478165 3185455619494227100323707)
      ·
        refine ⟨4778183429241340650485561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3185455619494227100323707 4778183429241340650485561)
        ·
          refine ⟨3583637571931005487864171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4778183429241340650485561 3583637571931005487864171)
          ·
            refine ⟨5375456357896508231796257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3583637571931005487864171 5375456357896508231796257)
            ·
              refine ⟨4031592268422381173847193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5375456357896508231796257 4031592268422381173847193)
              ·
                refine ⟨3023694201316785880385395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4031592268422381173847193 3023694201316785880385395)
                ·
                  refine ⟨4535541301975178820578093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023694201316785880385395 4535541301975178820578093)
                  ·
                    refine ⟨1700827988240692057716785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4535541301975178820578093 1700827988240692057716785)
                    ·
                      refine ⟨1275620991180519043287589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700827988240692057716785 1275620991180519043287589)
                      ·
                        rfl

theorem cell23_2484263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_2484263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484263 prefixEnd_2484263 := by exact prefixLift 2484263
  have htrace : WordTrace (prefixWord ++ tailWord_2484263) baseStart_2484263 baseEnd_2484263 := by
    simpa [prefixWord, tailWord_2484263, baseEnd_2484263] using wordTrace_append hprefix tailTrace_2484263
  have hstable : (prefixWord ++ tailWord_2484263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484263).length < 2 ^ (prefixWord ++ tailWord_2484263).sum := by decide
  have hdescent : baseEnd_2484263 < baseStart_2484263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484275 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 3]
def baseStart_2484275 : Nat := 118140960795 + 2484275 * 2 ^ 59
def prefixEnd_2484275 : Nat := 4983230072969 + 3 ^ 40 * 2484275 * 2
def baseEnd_2484275 : Nat := 1275627152948372996337533

theorem tailTrace_2484275 : CollatzResearch.WordTrace tailWord_2484275 prefixEnd_2484275 1275627152948372996337533 := by
  unfold tailWord_2484275
  simp only [CollatzResearch.WordTrace]
  refine ⟨90608953074903430236422279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60405968716602286824281519 90608953074903430236422279)
  ·
    refine ⟨135913429612355145354633419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90608953074903430236422279 135913429612355145354633419)
    ·
      refine ⟨203870144418532718031950129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135913429612355145354633419 203870144418532718031950129)
      ·
        refine ⟨152902608313899538523962597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203870144418532718031950129 152902608313899538523962597)
        ·
          refine ⟨28669239058856163473242987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152902608313899538523962597 28669239058856163473242987)
          ·
            refine ⟨43003858588284245209864481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28669239058856163473242987 43003858588284245209864481)
            ·
              refine ⟨32252893941213183907398361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43003858588284245209864481 32252893941213183907398361)
              ·
                refine ⟨24189670455909887930548771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32252893941213183907398361 24189670455909887930548771)
                ·
                  refine ⟨36284505683864831895823157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24189670455909887930548771 36284505683864831895823157)
                  ·
                    refine ⟨3401672407862327990233421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36284505683864831895823157 3401672407862327990233421)
                    ·
                      refine ⟨1275627152948372996337533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3401672407862327990233421 1275627152948372996337533)
                      ·
                        rfl

theorem cell23_2484275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 5, 3].length) (baseStart_2484275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484275 prefixEnd_2484275 := by exact prefixLift 2484275
  have htrace : WordTrace (prefixWord ++ tailWord_2484275) baseStart_2484275 baseEnd_2484275 := by
    simpa [prefixWord, tailWord_2484275, baseEnd_2484275] using wordTrace_append hprefix tailTrace_2484275
  have hstable : (prefixWord ++ tailWord_2484275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484275).length < 2 ^ (prefixWord ++ tailWord_2484275).sum := by decide
  have hdescent : baseEnd_2484275 < baseStart_2484275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484310 : List Nat := [5, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_2484310 : Nat := 118140960795 + 2484310 * 2 ^ 59
def prefixEnd_2484310 : Nat := 4983230072969 + 3 ^ 40 * 2484310 * 2
def baseEnd_2484310 : Nat := 1275645124771280359399873

theorem tailTrace_2484310 : CollatzResearch.WordTrace tailWord_2484310 prefixEnd_2484310 1275645124771280359399873 := by
  unfold tailWord_2484310
  simp only [CollatzResearch.WordTrace]
  refine ⟨5663139351861039450871649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60406819753184420809297589 5663139351861039450871649)
  ·
    refine ⟨4247354513895779588153737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5663139351861039450871649 4247354513895779588153737)
    ·
      refine ⟨3185515885421834691115303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4247354513895779588153737 3185515885421834691115303)
      ·
        refine ⟨4778273828132752036672955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3185515885421834691115303 4778273828132752036672955)
        ·
          refine ⟨7167410742199128055009433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4778273828132752036672955 7167410742199128055009433)
          ·
            refine ⟨5375558056649346041257075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7167410742199128055009433 5375558056649346041257075)
            ·
              refine ⟨8063337084974019061885613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5375558056649346041257075 8063337084974019061885613)
              ·
                refine ⟨3023751406865257148207105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8063337084974019061885613 3023751406865257148207105)
                ·
                  refine ⟨2267813555148942861155329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3023751406865257148207105 2267813555148942861155329)
                  ·
                    refine ⟨1700860166361707145866497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2267813555148942861155329 1700860166361707145866497)
                    ·
                      refine ⟨1275645124771280359399873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700860166361707145866497 1275645124771280359399873)
                      ·
                        rfl

theorem cell23_2484310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_2484310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484310 prefixEnd_2484310 := by exact prefixLift 2484310
  have htrace : WordTrace (prefixWord ++ tailWord_2484310) baseStart_2484310 baseEnd_2484310 := by
    simpa [prefixWord, tailWord_2484310, baseEnd_2484310] using wordTrace_append hprefix tailTrace_2484310
  have hstable : (prefixWord ++ tailWord_2484310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484310).length < 2 ^ (prefixWord ++ tailWord_2484310).sum := by decide
  have hdescent : baseEnd_2484310 < baseStart_2484310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484332 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 4]
def baseStart_2484332 : Nat := 118140960795 + 2484332 * 2 ^ 59
def prefixEnd_2484332 : Nat := 4983230072969 + 3 ^ 40 * 2484332 * 2
def baseEnd_2484332 : Nat := 1275656421345679273324771

theorem tailTrace_2484332 : CollatzResearch.WordTrace tailWord_2484332 prefixEnd_2484332 1275656421345679273324771 := by
  unfold tailWord_2484332
  simp only [CollatzResearch.WordTrace]
  refine ⟨45305516017848464485623625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60407354690464619314164833 45305516017848464485623625)
  ·
    refine ⟨33979137013386348364217719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45305516017848464485623625 33979137013386348364217719)
    ·
      refine ⟨50968705520079522546326579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33979137013386348364217719 50968705520079522546326579)
      ·
        refine ⟨76453058280119283819489869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50968705520079522546326579 76453058280119283819489869)
        ·
          refine ⟨28669896855044731432308701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76453058280119283819489869 28669896855044731432308701)
          ·
            refine ⟨10751211320641774287115763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28669896855044731432308701 10751211320641774287115763)
            ·
              refine ⟨16126816980962661430673645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10751211320641774287115763 16126816980962661430673645)
              ·
                refine ⟨6047556367860998036502617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16126816980962661430673645 6047556367860998036502617)
                ·
                  refine ⟨4535667275895748527376963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6047556367860998036502617 4535667275895748527376963)
                  ·
                    refine ⟨6803500913843622791065445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4535667275895748527376963 6803500913843622791065445)
                    ·
                      refine ⟨1275656421345679273324771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6803500913843622791065445 1275656421345679273324771)
                      ·
                        rfl

theorem cell23_2484332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_2484332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484332 prefixEnd_2484332 := by exact prefixLift 2484332
  have htrace : WordTrace (prefixWord ++ tailWord_2484332) baseStart_2484332 baseEnd_2484332 := by
    simpa [prefixWord, tailWord_2484332, baseEnd_2484332] using wordTrace_append hprefix tailTrace_2484332
  have hstable : (prefixWord ++ tailWord_2484332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484332).length < 2 ^ (prefixWord ++ tailWord_2484332).sum := by decide
  have hdescent : baseEnd_2484332 < baseStart_2484332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484366 : List Nat := [4, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2]
def baseStart_2484366 : Nat := 118140960795 + 2484366 * 2 ^ 59
def prefixEnd_2484366 : Nat := 4983230072969 + 3 ^ 40 * 2484366 * 2
def baseEnd_2484366 : Nat := 1275673879687932140299615

theorem tailTrace_2484366 : CollatzResearch.WordTrace tailWord_2484366 prefixEnd_2484366 1275673879687932140299615 := by
  unfold tailWord_2484366
  simp only [CollatzResearch.WordTrace]
  refine ⟨11326534014696719097248119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60408181411715835185323301 11326534014696719097248119)
  ·
    refine ⟨16989801022045078645872179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11326534014696719097248119 16989801022045078645872179)
    ·
      refine ⟨25484701533067617968808269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16989801022045078645872179 25484701533067617968808269)
      ·
        refine ⟨9556763074900356738303101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25484701533067617968808269 9556763074900356738303101)
        ·
          refine ⟨3583786153087633776863663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9556763074900356738303101 3583786153087633776863663)
          ·
            refine ⟨5375679229631450665295495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3583786153087633776863663 5375679229631450665295495)
            ·
              refine ⟨8063518844447175997943243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5375679229631450665295495 8063518844447175997943243)
              ·
                refine ⟨12095278266670763996914865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8063518844447175997943243 12095278266670763996914865)
                ·
                  refine ⟨9071458700003072997686149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12095278266670763996914865 9071458700003072997686149)
                  ·
                    refine ⟨1700898506250576187066153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9071458700003072997686149 1700898506250576187066153)
                    ·
                      refine ⟨1275673879687932140299615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700898506250576187066153 1275673879687932140299615)
                      ·
                        rfl

theorem cell23_2484366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_2484366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484366 prefixEnd_2484366 := by exact prefixLift 2484366
  have htrace : WordTrace (prefixWord ++ tailWord_2484366) baseStart_2484366 baseEnd_2484366 := by
    simpa [prefixWord, tailWord_2484366, baseEnd_2484366] using wordTrace_append hprefix tailTrace_2484366
  have hstable : (prefixWord ++ tailWord_2484366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484366).length < 2 ^ (prefixWord ++ tailWord_2484366).sum := by decide
  have hdescent : baseEnd_2484366 < baseStart_2484366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484386 : List Nat := [3, 3, 1, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_2484386 : Nat := 118140960795 + 2484386 * 2 ^ 59
def prefixEnd_2484386 : Nat := 4983230072969 + 3 ^ 40 * 2484386 * 2
def baseEnd_2484386 : Nat := 1275684149301022062049523

theorem tailTrace_2484386 : CollatzResearch.WordTrace tailWord_2484386 prefixEnd_2484386 1275684149301022062049523 := by
  unfold tailWord_2484386
  simp only [CollatzResearch.WordTrace]
  refine ⟨22653250394375324048428253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60408667718334197462475341 22653250394375324048428253)
  ·
    refine ⟨8494968897890746518160595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22653250394375324048428253 8494968897890746518160595)
    ·
      refine ⟨12742453346836119777240893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8494968897890746518160595 12742453346836119777240893)
      ·
        refine ⟨4778420005063544916465335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12742453346836119777240893 4778420005063544916465335)
        ·
          refine ⟨7167630007595317374698003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4778420005063544916465335 7167630007595317374698003)
          ·
            refine ⟨10751445011392976062047005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7167630007595317374698003 10751445011392976062047005)
            ·
              refine ⟨4031791879272366023267627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10751445011392976062047005 4031791879272366023267627)
              ·
                refine ⟨6047687818908549034901441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4031791879272366023267627 6047687818908549034901441)
                ·
                  refine ⟨4535765864181411776176081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6047687818908549034901441 4535765864181411776176081)
                  ·
                    refine ⟨3401824398136058832132061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4535765864181411776176081 3401824398136058832132061)
                    ·
                      refine ⟨1275684149301022062049523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3401824398136058832132061 1275684149301022062049523)
                      ·
                        rfl

theorem cell23_2484386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_2484386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484386 prefixEnd_2484386 := by exact prefixLift 2484386
  have htrace : WordTrace (prefixWord ++ tailWord_2484386) baseStart_2484386 baseEnd_2484386 := by
    simpa [prefixWord, tailWord_2484386, baseEnd_2484386] using wordTrace_append hprefix tailTrace_2484386
  have hstable : (prefixWord ++ tailWord_2484386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484386).length < 2 ^ (prefixWord ++ tailWord_2484386).sum := by decide
  have hdescent : baseEnd_2484386 < baseStart_2484386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484409 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 4, 3, 2]
def baseStart_2484409 : Nat := 118140960795 + 2484409 * 2 ^ 59
def prefixEnd_2484409 : Nat := 4983230072969 + 3 ^ 40 * 2484409 * 2
def baseEnd_2484409 : Nat := 1275695959356075472061917

theorem tailTrace_2484409 : CollatzResearch.WordTrace tailWord_2484409 prefixEnd_2484409 1275695959356075472061917 := by
  unfold tailWord_2484409
  simp only [CollatzResearch.WordTrace]
  refine ⟨90613840456417971121800281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60409226970945314081200187 90613840456417971121800281)
  ·
    refine ⟨67960380342313478341350211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90613840456417971121800281 67960380342313478341350211)
    ·
      refine ⟨101940570513470217512025317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67960380342313478341350211 101940570513470217512025317)
      ·
        refine ⟨19113856971275665783504747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101940570513470217512025317 19113856971275665783504747)
        ·
          refine ⟨28670785456913498675257121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19113856971275665783504747 28670785456913498675257121)
          ·
            refine ⟨21503089092685124006442841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28670785456913498675257121 21503089092685124006442841)
            ·
              refine ⟨16127316819513843004832131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21503089092685124006442841 16127316819513843004832131)
              ·
                refine ⟨24190975229270764507248197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16127316819513843004832131 24190975229270764507248197)
                ·
                  refine ⟨4535807855488268345109037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24190975229270764507248197 4535807855488268345109037)
                  ·
                    refine ⟨1700927945808100629415889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4535807855488268345109037 1700927945808100629415889)
                    ·
                      refine ⟨1275695959356075472061917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1700927945808100629415889 1275695959356075472061917)
                      ·
                        rfl

theorem cell23_2484409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_2484409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484409 prefixEnd_2484409 := by exact prefixLift 2484409
  have htrace : WordTrace (prefixWord ++ tailWord_2484409) baseStart_2484409 baseEnd_2484409 := by
    simpa [prefixWord, tailWord_2484409, baseEnd_2484409] using wordTrace_append hprefix tailTrace_2484409
  have hstable : (prefixWord ++ tailWord_2484409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484409).length < 2 ^ (prefixWord ++ tailWord_2484409).sum := by decide
  have hdescent : baseEnd_2484409 < baseStart_2484409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484416 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 3, 1, 3]
def baseStart_2484416 : Nat := 118140960795 + 2484416 * 2 ^ 59
def prefixEnd_2484416 : Nat := 4983230072969 + 3 ^ 40 * 2484416 * 2
def baseEnd_2484416 : Nat := 1275699553720656944674385

theorem tailTrace_2484416 : CollatzResearch.WordTrace tailWord_2484416 prefixEnd_2484416 1275699553720656944674385 := by
  unfold tailWord_2484416
  simp only [CollatzResearch.WordTrace]
  refine ⟨45307047883696305658652551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60409397178261740878203401 45307047883696305658652551)
  ·
    refine ⟨67960571825544458487978827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45307047883696305658652551 67960571825544458487978827)
    ·
      refine ⟨101940857738316687731968241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67960571825544458487978827 101940857738316687731968241)
      ·
        refine ⟨76455643303737515798976181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101940857738316687731968241 76455643303737515798976181)
        ·
          refine ⟨7167716559725392106154017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76455643303737515798976181 7167716559725392106154017)
          ·
            refine ⟨5375787419794044079615513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7167716559725392106154017 5375787419794044079615513)
            ·
              refine ⟨4031840564845533059711635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5375787419794044079615513 4031840564845533059711635)
              ·
                refine ⟨6047760847268299589567453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4031840564845533059711635 6047760847268299589567453)
                ·
                  refine ⟨2267910317725612346087795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6047760847268299589567453 2267910317725612346087795)
                  ·
                    refine ⟨3401865476588418519131693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2267910317725612346087795 3401865476588418519131693)
                    ·
                      refine ⟨1275699553720656944674385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3401865476588418519131693 1275699553720656944674385)
                      ·
                        rfl

theorem cell23_2484416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_2484416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484416 prefixEnd_2484416 := by exact prefixLift 2484416
  have htrace : WordTrace (prefixWord ++ tailWord_2484416) baseStart_2484416 baseEnd_2484416 := by
    simpa [prefixWord, tailWord_2484416, baseEnd_2484416] using wordTrace_append hprefix tailTrace_2484416
  have hstable : (prefixWord ++ tailWord_2484416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484416).length < 2 ^ (prefixWord ++ tailWord_2484416).sum := by decide
  have hdescent : baseEnd_2484416 < baseStart_2484416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484452 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_2484452 : Nat := 118140960795 + 2484452 * 2 ^ 59
def prefixEnd_2484452 : Nat := 4983230072969 + 3 ^ 40 * 2484452 * 2
def baseEnd_2484452 : Nat := 1275718039024218803824219

theorem tailTrace_2484452 : CollatzResearch.WordTrace tailWord_2484452 prefixEnd_2484452 1275718039024218803824219 := by
  unfold tailWord_2484452
  simp only [CollatzResearch.WordTrace]
  refine ⟨45307704397631094732807805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60410272530174792977077073 45307704397631094732807805)
  ·
    refine ⟨16990389149111660524802927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45307704397631094732807805 16990389149111660524802927)
    ·
      refine ⟨25485583723667490787204391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16990389149111660524802927 25485583723667490787204391)
      ·
        refine ⟨38228375585501236180806587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25485583723667490787204391 38228375585501236180806587)
        ·
          refine ⟨57342563378251854271209881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38228375585501236180806587 57342563378251854271209881)
          ·
            refine ⟨43006922533688890703407411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57342563378251854271209881 43006922533688890703407411)
            ·
              refine ⟨64510383800533336055111117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43006922533688890703407411 64510383800533336055111117)
              ·
                refine ⟨24191393925200001020666669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64510383800533336055111117 24191393925200001020666669)
                ·
                  refine ⟨9071772721950000382750001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24191393925200001020666669 9071772721950000382750001)
                  ·
                    refine ⟨6803829541462500287062501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9071772721950000382750001 6803829541462500287062501)
                    ·
                      refine ⟨1275718039024218803824219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6803829541462500287062501 1275718039024218803824219)
                      ·
                        rfl

theorem cell23_2484452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_2484452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484452 prefixEnd_2484452 := by exact prefixLift 2484452
  have htrace : WordTrace (prefixWord ++ tailWord_2484452) baseStart_2484452 baseEnd_2484452 := by
    simpa [prefixWord, tailWord_2484452, baseEnd_2484452] using wordTrace_append hprefix tailTrace_2484452
  have hstable : (prefixWord ++ tailWord_2484452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484452).length < 2 ^ (prefixWord ++ tailWord_2484452).sum := by decide
  have hdescent : baseEnd_2484452 < baseStart_2484452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484459 : List Nat := [1, 1, 1, 1, 2, 5, 1, 5, 1, 2, 3]
def baseStart_2484459 : Nat := 118140960795 + 2484459 * 2 ^ 59
def prefixEnd_2484459 : Nat := 4983230072969 + 3 ^ 40 * 2484459 * 2
def baseEnd_2484459 : Nat := 1275721633388800276436687

theorem tailTrace_2484459 : CollatzResearch.WordTrace tailWord_2484459 prefixEnd_2484459 1275721633388800276436687 := by
  unfold tailWord_2484459
  simp only [CollatzResearch.WordTrace]
  refine ⟨90615664106236829661120431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60410442737491219774080287 90615664106236829661120431)
  ·
    refine ⟨135923496159355244491680647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90615664106236829661120431 135923496159355244491680647)
    ·
      refine ⟨203885244239032866737520971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135923496159355244491680647 203885244239032866737520971)
      ·
        refine ⟨305827866358549300106281457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203885244239032866737520971 305827866358549300106281457)
        ·
          refine ⟨229370899768911975079711093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305827866358549300106281457 229370899768911975079711093)
          ·
            refine ⟨21503521853335497663722915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 229370899768911975079711093 21503521853335497663722915)
            ·
              refine ⟨32255282780003246495584373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21503521853335497663722915 32255282780003246495584373)
              ·
                refine ⟨3023932760625304358961035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32255282780003246495584373 3023932760625304358961035)
                ·
                  refine ⟨4535899140937956538441553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023932760625304358961035 4535899140937956538441553)
                  ·
                    refine ⟨3401924355703467403831165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4535899140937956538441553 3401924355703467403831165)
                    ·
                      refine ⟨1275721633388800276436687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3401924355703467403831165 1275721633388800276436687)
                      ·
                        rfl

theorem cell23_2484459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 2, 3].length) (baseStart_2484459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484459 prefixEnd_2484459 := by exact prefixLift 2484459
  have htrace : WordTrace (prefixWord ++ tailWord_2484459) baseStart_2484459 baseEnd_2484459 := by
    simpa [prefixWord, tailWord_2484459, baseEnd_2484459] using wordTrace_append hprefix tailTrace_2484459
  have hstable : (prefixWord ++ tailWord_2484459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484459).length < 2 ^ (prefixWord ++ tailWord_2484459).sum := by decide
  have hdescent : baseEnd_2484459 < baseStart_2484459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484506 : List Nat := [3, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3]
def baseStart_2484506 : Nat := 118140960795 + 2484506 * 2 ^ 59
def prefixEnd_2484506 : Nat := 4983230072969 + 3 ^ 40 * 2484506 * 2
def baseEnd_2484506 : Nat := 1275745766979561592548971

theorem tailTrace_2484506 : CollatzResearch.WordTrace tailWord_2484506 prefixEnd_2484506 1275745766979561592548971 := by
  unfold tailWord_2484506
  simp only [CollatzResearch.WordTrace]
  refine ⟨22654344584266639172020343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60411585558044371125387581 22654344584266639172020343)
  ·
    refine ⟨33981516876399958758030515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22654344584266639172020343 33981516876399958758030515)
    ·
      refine ⟨50972275314599938137045773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33981516876399958758030515 50972275314599938137045773)
      ·
        refine ⟨19114603242974976801392165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50972275314599938137045773 19114603242974976801392165)
        ·
          refine ⟨3583988108057808150261031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19114603242974976801392165 3583988108057808150261031)
          ·
            refine ⟨5375982162086712225391547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3583988108057808150261031 5375982162086712225391547)
            ·
              refine ⟨8063973243130068338087321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5375982162086712225391547 8063973243130068338087321)
              ·
                refine ⟨6047979932347551253565491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8063973243130068338087321 6047979932347551253565491)
                ·
                  refine ⟨9071969898521326880348237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6047979932347551253565491 9071969898521326880348237)
                  ·
                    refine ⟨3401988711945497580130589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9071969898521326880348237 3401988711945497580130589)
                    ·
                      refine ⟨1275745766979561592548971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3401988711945497580130589 1275745766979561592548971)
                      ·
                        rfl

theorem cell23_2484506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_2484506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484506 prefixEnd_2484506 := by exact prefixLift 2484506
  have htrace : WordTrace (prefixWord ++ tailWord_2484506) baseStart_2484506 baseEnd_2484506 := by
    simpa [prefixWord, tailWord_2484506, baseEnd_2484506] using wordTrace_append hprefix tailTrace_2484506
  have hstable : (prefixWord ++ tailWord_2484506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484506).length < 2 ^ (prefixWord ++ tailWord_2484506).sum := by decide
  have hdescent : baseEnd_2484506 < baseStart_2484506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484552 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 9]
def baseStart_2484552 : Nat := 118140960795 + 2484552 * 2 ^ 59
def prefixEnd_2484552 : Nat := 4983230072969 + 3 ^ 40 * 2484552 * 2
def baseEnd_2484552 : Nat := 141752154121074268063751

theorem tailTrace_2484552 : CollatzResearch.WordTrace tailWord_2484552 prefixEnd_2484552 141752154121074268063751 := by
  unfold tailWord_2484552
  simp only [CollatzResearch.WordTrace]
  refine ⟨45309528047449953272127955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60412704063266604362837273 45309528047449953272127955)
  ·
    refine ⟨67964292071174929908191933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45309528047449953272127955 67964292071174929908191933)
    ·
      refine ⟨25486609526690598715571975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67964292071174929908191933 25486609526690598715571975)
      ·
        refine ⟨38229914290035898073357963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25486609526690598715571975 38229914290035898073357963)
        ·
          refine ⟨57344871435053847110036945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38229914290035898073357963 57344871435053847110036945)
          ·
            refine ⟨43008653576290385332527709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57344871435053847110036945 43008653576290385332527709)
            ·
              refine ⟨16128245091108894499697891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43008653576290385332527709 16128245091108894499697891)
              ·
                refine ⟨24192367636663341749546837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16128245091108894499697891 24192367636663341749546837)
                ·
                  refine ⟨141752154121074268063751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 24192367636663341749546837 141752154121074268063751)
                  ·
                    rfl

theorem cell23_2484552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 9].length) (baseStart_2484552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484552 prefixEnd_2484552 := by exact prefixLift 2484552
  have htrace : WordTrace (prefixWord ++ tailWord_2484552) baseStart_2484552 baseEnd_2484552 := by
    simpa [prefixWord, tailWord_2484552, baseEnd_2484552] using wordTrace_append hprefix tailTrace_2484552
  have hstable : (prefixWord ++ tailWord_2484552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484552).length < 2 ^ (prefixWord ++ tailWord_2484552).sum := by decide
  have hdescent : baseEnd_2484552 < baseStart_2484552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484574 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_2484574 : Nat := 118140960795 + 2484574 * 2 ^ 59
def prefixEnd_2484574 : Nat := 4983230072969 + 3 ^ 40 * 2484574 * 2
def baseEnd_2484574 : Nat := 1275780683664067326498659

theorem tailTrace_2484574 : CollatzResearch.WordTrace tailWord_2484574 prefixEnd_2484574 1275780683664067326498659 := by
  unfold tailWord_2484574
  simp only [CollatzResearch.WordTrace]
  refine ⟨11327482312602525537694597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60413239000546802867704517 11327482312602525537694597)
  ·
    refine ⟨2123902933612973538317737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11327482312602525537694597 2123902933612973538317737)
    ·
      refine ⟨1592927200209730153738303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2123902933612973538317737 1592927200209730153738303)
      ·
        refine ⟨2389390800314595230607455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1592927200209730153738303 2389390800314595230607455)
        ·
          refine ⟨3584086200471892845911183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2389390800314595230607455 3584086200471892845911183)
          ·
            refine ⟨5376129300707839268866775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3584086200471892845911183 5376129300707839268866775)
            ·
              refine ⟨8064193951061758903300163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5376129300707839268866775 8064193951061758903300163)
              ·
                refine ⟨12096290926592638354950245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8064193951061758903300163 12096290926592638354950245)
                ·
                  refine ⟨2268054548736119691553171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12096290926592638354950245 2268054548736119691553171)
                  ·
                    refine ⟨3402081823104179537329757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2268054548736119691553171 3402081823104179537329757)
                    ·
                      refine ⟨1275780683664067326498659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3402081823104179537329757 1275780683664067326498659)
                      ·
                        rfl

theorem cell23_2484574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_2484574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484574 prefixEnd_2484574 := by exact prefixLift 2484574
  have htrace : WordTrace (prefixWord ++ tailWord_2484574) baseStart_2484574 baseEnd_2484574 := by
    simpa [prefixWord, tailWord_2484574, baseEnd_2484574] using wordTrace_append hprefix tailTrace_2484574
  have hstable : (prefixWord ++ tailWord_2484574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484574).length < 2 ^ (prefixWord ++ tailWord_2484574).sum := by decide
  have hdescent : baseEnd_2484574 < baseStart_2484574 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484579 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 3]
def baseStart_2484579 : Nat := 118140960795 + 2484579 * 2 ^ 59
def prefixEnd_2484579 : Nat := 4983230072969 + 3 ^ 40 * 2484579 * 2
def baseEnd_2484579 : Nat := 1275783251067339806936135

theorem tailTrace_2484579 : CollatzResearch.WordTrace tailWord_2484579 prefixEnd_2484579 1275783251067339806936135 := by
  unfold tailWord_2484579
  simp only [CollatzResearch.WordTrace]
  refine ⟨90620040865802090155488791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60413360577201393436992527 90620040865802090155488791)
  ·
    refine ⟨135930061298703135233233187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90620040865802090155488791 135930061298703135233233187)
    ·
      refine ⟨203895091948054702849849781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135930061298703135233233187 203895091948054702849849781)
      ·
        refine ⟨19115164870130128392173417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203895091948054702849849781 19115164870130128392173417)
        ·
          refine ⟨14336373652597596294130063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19115164870130128392173417 14336373652597596294130063)
          ·
            refine ⟨21504560478896394441195095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14336373652597596294130063 21504560478896394441195095)
            ·
              refine ⟨32256840718344591661792643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21504560478896394441195095 32256840718344591661792643)
              ·
                refine ⟨48385261077516887492688965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32256840718344591661792643 48385261077516887492688965)
                ·
                  refine ⟨9072236452034416404879181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48385261077516887492688965 9072236452034416404879181)
                  ·
                    refine ⟨3402088669512906151829693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9072236452034416404879181 3402088669512906151829693)
                    ·
                      refine ⟨1275783251067339806936135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3402088669512906151829693 1275783251067339806936135)
                      ·
                        rfl

theorem cell23_2484579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_2484579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484579 prefixEnd_2484579 := by exact prefixLift 2484579
  have htrace : WordTrace (prefixWord ++ tailWord_2484579) baseStart_2484579 baseEnd_2484579 := by
    simpa [prefixWord, tailWord_2484579, baseEnd_2484579] using wordTrace_append hprefix tailTrace_2484579
  have hstable : (prefixWord ++ tailWord_2484579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484579).length < 2 ^ (prefixWord ++ tailWord_2484579).sum := by decide
  have hdescent : baseEnd_2484579 < baseStart_2484579 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484586 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 7]
def baseStart_2484586 : Nat := 118140960795 + 2484586 * 2 ^ 59
def prefixEnd_2484586 : Nat := 4983230072969 + 3 ^ 40 * 2484586 * 2
def baseEnd_2484586 : Nat := 141754093936880142172067

theorem tailTrace_2484586 : CollatzResearch.WordTrace tailWord_2484586 prefixEnd_2484586 141754093936880142172067 := by
  unfold tailWord_2484586
  simp only [CollatzResearch.WordTrace]
  refine ⟨22655074044194182587748403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60413530784517820233995741 22655074044194182587748403)
  ·
    refine ⟨33982611066291273881622605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22655074044194182587748403 33982611066291273881622605)
    ·
      refine ⟨12743479149859227705608477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33982611066291273881622605 12743479149859227705608477)
      ·
        refine ⟨4778804681197210389603179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12743479149859227705608477 4778804681197210389603179)
        ·
          refine ⟨7168207021795815584404769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4778804681197210389603179 7168207021795815584404769)
          ·
            refine ⟨5376155266346861688303577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7168207021795815584404769 5376155266346861688303577)
            ·
              refine ⟨4032116449760146266227683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5376155266346861688303577 4032116449760146266227683)
              ·
                refine ⟨6048174674640219399341525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4032116449760146266227683 6048174674640219399341525)
                ·
                  refine ⟨141754093936880142172067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6048174674640219399341525 141754093936880142172067)
                  ·
                    rfl

theorem cell23_2484586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 7].length) (baseStart_2484586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484586 prefixEnd_2484586 := by exact prefixLift 2484586
  have htrace : WordTrace (prefixWord ++ tailWord_2484586) baseStart_2484586 baseEnd_2484586 := by
    simpa [prefixWord, tailWord_2484586, baseEnd_2484586] using wordTrace_append hprefix tailTrace_2484586
  have hstable : (prefixWord ++ tailWord_2484586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484586).length < 2 ^ (prefixWord ++ tailWord_2484586).sum := by decide
  have hdescent : baseEnd_2484586 < baseStart_2484586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484597 : List Nat := [1, 3, 4, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_2484597 : Nat := 118140960795 + 2484597 * 2 ^ 59
def prefixEnd_2484597 : Nat := 4983230072969 + 3 ^ 40 * 2484597 * 2
def baseEnd_2484597 : Nat := 1275792493719120736511053

theorem tailTrace_2484597 : CollatzResearch.WordTrace tailWord_2484597 prefixEnd_2484597 1275792493719120736511053 := by
  unfold tailWord_2484597
  simp only [CollatzResearch.WordTrace]
  refine ⟨90620697379736879229644045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60413798253157919486429363 90620697379736879229644045)
  ·
    refine ⟨33982761517401329711116517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90620697379736879229644045 33982761517401329711116517)
    ·
      refine ⟨6371767784512749320834347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33982761517401329711116517 6371767784512749320834347)
      ·
        refine ⟨9557651676769123981251521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6371767784512749320834347 9557651676769123981251521)
        ·
          refine ⟨7168238757576842985938641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9557651676769123981251521 7168238757576842985938641)
          ·
            refine ⟨5376179068182632239453981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7168238757576842985938641 5376179068182632239453981)
            ·
              refine ⟨2016067150568487089795243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5376179068182632239453981 2016067150568487089795243)
              ·
                refine ⟨3024100725852730634692865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2016067150568487089795243 3024100725852730634692865)
                ·
                  refine ⟨2268075544389547976019649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3024100725852730634692865 2268075544389547976019649)
                  ·
                    refine ⟨1701056658292160982014737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2268075544389547976019649 1701056658292160982014737)
                    ·
                      refine ⟨1275792493719120736511053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1701056658292160982014737 1275792493719120736511053)
                      ·
                        rfl

theorem cell23_2484597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_2484597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484597 prefixEnd_2484597 := by exact prefixLift 2484597
  have htrace : WordTrace (prefixWord ++ tailWord_2484597) baseStart_2484597 baseEnd_2484597 := by
    simpa [prefixWord, tailWord_2484597, baseEnd_2484597] using wordTrace_append hprefix tailTrace_2484597
  have hstable : (prefixWord ++ tailWord_2484597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484597).length < 2 ^ (prefixWord ++ tailWord_2484597).sum := by decide
  have hdescent : baseEnd_2484597 < baseStart_2484597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484619 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 4]
def baseStart_2484619 : Nat := 118140960795 + 2484619 * 2 ^ 59
def prefixEnd_2484619 : Nat := 4983230072969 + 3 ^ 40 * 2484619 * 2
def baseEnd_2484619 : Nat := 1275803790293519650435951

theorem tailTrace_2484619 : CollatzResearch.WordTrace tailWord_2484619 prefixEnd_2484619 1275803790293519650435951 := by
  unfold tailWord_2484619
  simp only [CollatzResearch.WordTrace]
  refine ⟨90621499785657176986944911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60414333190438117991296607 90621499785657176986944911)
  ·
    refine ⟨135932249678485765480417367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90621499785657176986944911 135932249678485765480417367)
    ·
      refine ⟨203898374517728648220626051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135932249678485765480417367 203898374517728648220626051)
      ·
        refine ⟨305847561776592972330939077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203898374517728648220626051 305847561776592972330939077)
        ·
          refine ⟨57346417833111182312051077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 305847561776592972330939077 57346417833111182312051077)
          ·
            refine ⟨10752453343708346683509577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57346417833111182312051077 10752453343708346683509577)
            ·
              refine ⟨8064340007781260012632183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10752453343708346683509577 8064340007781260012632183)
              ·
                refine ⟨12096510011671890018948275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8064340007781260012632183 12096510011671890018948275)
                ·
                  refine ⟨18144765017507835028422413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12096510011671890018948275 18144765017507835028422413)
                  ·
                    refine ⟨6804286881565438135658405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18144765017507835028422413 6804286881565438135658405)
                    ·
                      refine ⟨1275803790293519650435951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6804286881565438135658405 1275803790293519650435951)
                      ·
                        rfl

theorem cell23_2484619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 4].length) (baseStart_2484619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484619 prefixEnd_2484619 := by exact prefixLift 2484619
  have htrace : WordTrace (prefixWord ++ tailWord_2484619) baseStart_2484619 baseEnd_2484619 := by
    simpa [prefixWord, tailWord_2484619, baseEnd_2484619] using wordTrace_append hprefix tailTrace_2484619
  have hstable : (prefixWord ++ tailWord_2484619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484619).length < 2 ^ (prefixWord ++ tailWord_2484619).sum := by decide
  have hdescent : baseEnd_2484619 < baseStart_2484619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484696 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 3, 5, 2]
def baseStart_2484696 : Nat := 118140960795 + 2484696 * 2 ^ 59
def prefixEnd_2484696 : Nat := 4983230072969 + 3 ^ 40 * 2484696 * 2
def baseEnd_2484696 : Nat := 1275843328303915849173097

theorem tailTrace_2484696 : CollatzResearch.WordTrace tailWord_2484696 prefixEnd_2484696 1275843328303915849173097 := by
  unfold tailWord_2484696
  simp only [CollatzResearch.WordTrace]
  refine ⟨45312154103189109568748971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60416205470918812758331961 45312154103189109568748971)
  ·
    refine ⟨67968231154783664353123457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45312154103189109568748971 67968231154783664353123457)
    ·
      refine ⟨50976173366087748264842593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67968231154783664353123457 50976173366087748264842593)
      ·
        refine ⟨38232130024565811198631945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50976173366087748264842593 38232130024565811198631945)
        ·
          refine ⟨28674097518424358398973959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38232130024565811198631945 28674097518424358398973959)
          ·
            refine ⟨43011146277636537598460939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28674097518424358398973959 43011146277636537598460939)
            ·
              refine ⟨64516719416454806397691409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43011146277636537598460939 64516719416454806397691409)
              ·
                refine ⟨48387539562341104798268557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64516719416454806397691409 48387539562341104798268557)
                ·
                  refine ⟨18145327335877914299350709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48387539562341104798268557 18145327335877914299350709)
                  ·
                    refine ⟨1701124437738554465564129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18145327335877914299350709 1701124437738554465564129)
                    ·
                      refine ⟨1275843328303915849173097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1701124437738554465564129 1275843328303915849173097)
                      ·
                        rfl

theorem cell23_2484696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 5, 2].length) (baseStart_2484696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484696 prefixEnd_2484696 := by exact prefixLift 2484696
  have htrace : WordTrace (prefixWord ++ tailWord_2484696) baseStart_2484696 baseEnd_2484696 := by
    simpa [prefixWord, tailWord_2484696, baseEnd_2484696] using wordTrace_append hprefix tailTrace_2484696
  have hstable : (prefixWord ++ tailWord_2484696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484696).length < 2 ^ (prefixWord ++ tailWord_2484696).sum := by decide
  have hdescent : baseEnd_2484696 < baseStart_2484696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484737 : List Nat := [1, 2, 4, 1, 3, 2, 2, 3, 1, 1, 3]
def baseStart_2484737 : Nat := 118140960795 + 2484737 * 2 ^ 59
def prefixEnd_2484737 : Nat := 4983230072969 + 3 ^ 40 * 2484737 * 2
def baseEnd_2484737 : Nat := 1275864381010750188760409

theorem tailTrace_2484737 : CollatzResearch.WordTrace tailWord_2484737 prefixEnd_2484737 1275864381010750188760409 := by
  unfold tailWord_2484737
  simp only [CollatzResearch.WordTrace]
  refine ⟨90625803599229683139740465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60417202399486455426493643 90625803599229683139740465)
  ·
    refine ⟨67969352699422262354805349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90625803599229683139740465 67969352699422262354805349)
    ·
      refine ⟨12744253631141674191526003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67969352699422262354805349 12744253631141674191526003)
      ·
        refine ⟨19116380446712511287289005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12744253631141674191526003 19116380446712511287289005)
        ·
          refine ⟨7168642667517191732733377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19116380446712511287289005 7168642667517191732733377)
          ·
            refine ⟨5376482000637893799550033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7168642667517191732733377 5376482000637893799550033)
            ·
              refine ⟨4032361500478420349662525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5376482000637893799550033 4032361500478420349662525)
              ·
                refine ⟨1512135562679407631123447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4032361500478420349662525 1512135562679407631123447)
                ·
                  refine ⟨2268203344019111446685171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512135562679407631123447 2268203344019111446685171)
                  ·
                    refine ⟨3402305016028667170027757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2268203344019111446685171 3402305016028667170027757)
                    ·
                      refine ⟨1275864381010750188760409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3402305016028667170027757 1275864381010750188760409)
                      ·
                        rfl

theorem cell23_2484737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_2484737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484737 prefixEnd_2484737 := by exact prefixLift 2484737
  have htrace : WordTrace (prefixWord ++ tailWord_2484737) baseStart_2484737 baseEnd_2484737 := by
    simpa [prefixWord, tailWord_2484737, baseEnd_2484737] using wordTrace_append hprefix tailTrace_2484737
  have hstable : (prefixWord ++ tailWord_2484737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484737).length < 2 ^ (prefixWord ++ tailWord_2484737).sum := by decide
  have hdescent : baseEnd_2484737 < baseStart_2484737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484740 : List Nat := [2, 3, 2, 3, 1, 1, 4, 1, 1, 5]
def baseStart_2484740 : Nat := 118140960795 + 2484740 * 2 ^ 59
def prefixEnd_2484740 : Nat := 4983230072969 + 3 ^ 40 * 2484740 * 2
def baseEnd_2484740 : Nat := 425288640484237892340965

theorem tailTrace_2484740 : CollatzResearch.WordTrace tailWord_2484740 prefixEnd_2484740 425288640484237892340965 := by
  unfold tailWord_2484740
  simp only [CollatzResearch.WordTrace]
  refine ⟨45312956509109407326049837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60417275345479209768066449 45312956509109407326049837)
  ·
    refine ⟨16992358690916027747268689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45312956509109407326049837 16992358690916027747268689)
    ·
      refine ⟨12744269018187020810451517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16992358690916027747268689 12744269018187020810451517)
      ·
        refine ⟨4779100881820132803919319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12744269018187020810451517 4779100881820132803919319)
        ·
          refine ⟨7168651322730199205878979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4779100881820132803919319 7168651322730199205878979)
          ·
            refine ⟨10752976984095298808818469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7168651322730199205878979 10752976984095298808818469)
            ·
              refine ⟨2016183184517868526653463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10752976984095298808818469 2016183184517868526653463)
              ·
                refine ⟨3024274776776802789980195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2016183184517868526653463 3024274776776802789980195)
                ·
                  refine ⟨4536412165165204184970293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3024274776776802789980195 4536412165165204184970293)
                  ·
                    refine ⟨425288640484237892340965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4536412165165204184970293 425288640484237892340965)
                    ·
                      rfl

theorem cell23_2484740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_2484740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484740 prefixEnd_2484740 := by exact prefixLift 2484740
  have htrace : WordTrace (prefixWord ++ tailWord_2484740) baseStart_2484740 baseEnd_2484740 := by
    simpa [prefixWord, tailWord_2484740, baseEnd_2484740] using wordTrace_append hprefix tailTrace_2484740
  have hstable : (prefixWord ++ tailWord_2484740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484740).length < 2 ^ (prefixWord ++ tailWord_2484740).sum := by decide
  have hdescent : baseEnd_2484740 < baseStart_2484740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484746 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_2484746 : Nat := 118140960795 + 2484746 * 2 ^ 59
def prefixEnd_2484746 : Nat := 4983230072969 + 3 ^ 40 * 2484746 * 2
def baseEnd_2484746 : Nat := 1275869002336640653547867

theorem tailTrace_2484746 : CollatzResearch.WordTrace tailWord_2484746 prefixEnd_2484746 1275869002336640653547867 := by
  unfold tailWord_2484746
  simp only [CollatzResearch.WordTrace]
  refine ⟨22656532964049269419204523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60417421237464718451212061 22656532964049269419204523)
  ·
    refine ⟨33984799446073904128806785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22656532964049269419204523 33984799446073904128806785)
    ·
      refine ⟨25488599584555428096605089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33984799446073904128806785 25488599584555428096605089)
      ·
        refine ⟨19116449688416571072453817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25488599584555428096605089 19116449688416571072453817)
        ·
          refine ⟨14337337266312428304340363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19116449688416571072453817 14337337266312428304340363)
          ·
            refine ⟨21506005899468642456510545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14337337266312428304340363 21506005899468642456510545)
            ·
              refine ⟨16129504424601481842382909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21506005899468642456510545 16129504424601481842382909)
              ·
                refine ⟨6048564159225555690893591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16129504424601481842382909 6048564159225555690893591)
                ·
                  refine ⟨9072846238838333536340387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6048564159225555690893591 9072846238838333536340387)
                  ·
                    refine ⟨13609269358257500304510581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9072846238838333536340387 13609269358257500304510581)
                    ·
                      refine ⟨1275869002336640653547867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13609269358257500304510581 1275869002336640653547867)
                      ·
                        rfl

theorem cell23_2484746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_2484746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484746 prefixEnd_2484746 := by exact prefixLift 2484746
  have htrace : WordTrace (prefixWord ++ tailWord_2484746) baseStart_2484746 baseEnd_2484746 := by
    simpa [prefixWord, tailWord_2484746, baseEnd_2484746] using wordTrace_append hprefix tailTrace_2484746
  have hstable : (prefixWord ++ tailWord_2484746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484746).length < 2 ^ (prefixWord ++ tailWord_2484746).sum := by decide
  have hdescent : baseEnd_2484746 < baseStart_2484746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484760 : List Nat := [2, 1, 2, 3, 3, 1, 1, 3, 3, 2, 2]
def baseStart_2484760 : Nat := 118140960795 + 2484760 * 2 ^ 59
def prefixEnd_2484760 : Nat := 4983230072969 + 3 ^ 40 * 2484760 * 2
def baseEnd_2484760 : Nat := 1275876191065803598772803

theorem tailTrace_2484760 : CollatzResearch.WordTrace tailWord_2484760 prefixEnd_2484760 1275876191065803598772803 := by
  unfold tailWord_2484760
  simp only [CollatzResearch.WordTrace]
  refine ⟨45313321239073179033913867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60417761652097572045218489 45313321239073179033913867)
  ·
    refine ⟨67969981858609768550870801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45313321239073179033913867 67969981858609768550870801)
    ·
      refine ⟨50977486393957326413153101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67969981858609768550870801 50977486393957326413153101)
      ·
        refine ⟨19116557397733997404932413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50977486393957326413153101 19116557397733997404932413)
        ·
          refine ⟨7168709024150249026849655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19116557397733997404932413 7168709024150249026849655)
          ·
            refine ⟨10753063536225373540274483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7168709024150249026849655 10753063536225373540274483)
            ·
              refine ⟨16129595304338060310411725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10753063536225373540274483 16129595304338060310411725)
              ·
                refine ⟨6048598239126772616404397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16129595304338060310411725 6048598239126772616404397)
                ·
                  refine ⟨2268224339672539731151649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6048598239126772616404397 2268224339672539731151649)
                  ·
                    refine ⟨1701168254754404798363737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2268224339672539731151649 1701168254754404798363737)
                    ·
                      refine ⟨1275876191065803598772803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1701168254754404798363737 1275876191065803598772803)
                      ·
                        rfl

theorem cell23_2484760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_2484760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484760 prefixEnd_2484760 := by exact prefixLift 2484760
  have htrace : WordTrace (prefixWord ++ tailWord_2484760) baseStart_2484760 baseEnd_2484760 := by
    simpa [prefixWord, tailWord_2484760, baseEnd_2484760] using wordTrace_append hprefix tailTrace_2484760
  have hstable : (prefixWord ++ tailWord_2484760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484760).length < 2 ^ (prefixWord ++ tailWord_2484760).sum := by decide
  have hdescent : baseEnd_2484760 < baseStart_2484760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484779 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 2, 7]
def baseStart_2484779 : Nat := 118140960795 + 2484779 * 2 ^ 59
def prefixEnd_2484779 : Nat := 4983230072969 + 3 ^ 40 * 2484779 * 2
def baseEnd_2484779 : Nat := 425295315732746341478405

theorem tailTrace_2484779 : CollatzResearch.WordTrace tailWord_2484779 prefixEnd_2484779 425295315732746341478405 := by
  unfold tailWord_2484779
  simp only [CollatzResearch.WordTrace]
  refine ⟨90627335465077524312769391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60418223643385016208512927 90627335465077524312769391)
  ·
    refine ⟨135941003197616286469154087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90627335465077524312769391 135941003197616286469154087)
    ·
      refine ⟨203911504796424429703731131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135941003197616286469154087 203911504796424429703731131)
      ·
        refine ⟨305867257194636644555596697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203911504796424429703731131 305867257194636644555596697)
        ·
          refine ⟨229400442895977483416697523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305867257194636644555596697 229400442895977483416697523)
          ·
            refine ⟨344100664343966225125046285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229400442895977483416697523 344100664343966225125046285)
            ·
              refine ⟨129037749128987334421892357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 344100664343966225125046285 129037749128987334421892357)
              ·
                refine ⟨24194577961685125204104817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129037749128987334421892357 24194577961685125204104817)
                ·
                  refine ⟨18145933471263843903078613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24194577961685125204104817 18145933471263843903078613)
                  ·
                    refine ⟨425295315732746341478405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18145933471263843903078613 425295315732746341478405)
                    ·
                      rfl

theorem cell23_2484779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 2, 7].length) (baseStart_2484779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484779 prefixEnd_2484779 := by exact prefixLift 2484779
  have htrace : WordTrace (prefixWord ++ tailWord_2484779) baseStart_2484779 baseEnd_2484779 := by
    simpa [prefixWord, tailWord_2484779, baseEnd_2484779] using wordTrace_append hprefix tailTrace_2484779
  have hstable : (prefixWord ++ tailWord_2484779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484779).length < 2 ^ (prefixWord ++ tailWord_2484779).sum := by decide
  have hdescent : baseEnd_2484779 < baseStart_2484779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484788 : List Nat := [2, 5, 1, 3, 2, 1, 1, 3, 1, 1, 3]
def baseStart_2484788 : Nat := 118140960795 + 2484788 * 2 ^ 59
def prefixEnd_2484788 : Nat := 4983230072969 + 3 ^ 40 * 2484788 * 2
def baseEnd_2484788 : Nat := 1275890568524129489222675

theorem tailTrace_2484788 : CollatzResearch.WordTrace tailWord_2484788 prefixEnd_2484788 1275890568524129489222675 := by
  unfold tailWord_2484788
  simp only [CollatzResearch.WordTrace]
  refine ⟨45313831861022459424923509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60418442481363279233231345 45313831861022459424923509)
  ·
    refine ⟨4248171736970855571086579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45313831861022459424923509 4248171736970855571086579)
    ·
      refine ⟨6372257605456283356629869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4248171736970855571086579 6372257605456283356629869)
      ·
        refine ⟨2389596602046106258736201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6372257605456283356629869 2389596602046106258736201)
        ·
          refine ⟨1792197451534579694052151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2389596602046106258736201 1792197451534579694052151)
          ·
            refine ⟨2688296177301869541078227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792197451534579694052151 2688296177301869541078227)
            ·
              refine ⟨4032444265952804311617341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2688296177301869541078227 4032444265952804311617341)
              ·
                refine ⟨1512166599732301616856503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4032444265952804311617341 1512166599732301616856503)
                ·
                  refine ⟨2268249899598452425284755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512166599732301616856503 2268249899598452425284755)
                  ·
                    refine ⟨3402374849397678637927133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2268249899598452425284755 3402374849397678637927133)
                    ·
                      refine ⟨1275890568524129489222675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3402374849397678637927133 1275890568524129489222675)
                      ·
                        rfl

theorem cell23_2484788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_2484788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484788 prefixEnd_2484788 := by exact prefixLift 2484788
  have htrace : WordTrace (prefixWord ++ tailWord_2484788) baseStart_2484788 baseEnd_2484788 := by
    simpa [prefixWord, tailWord_2484788, baseEnd_2484788] using wordTrace_append hprefix tailTrace_2484788
  have hstable : (prefixWord ++ tailWord_2484788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484788).length < 2 ^ (prefixWord ++ tailWord_2484788).sum := by decide
  have hdescent : baseEnd_2484788 < baseStart_2484788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484793 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 6, 1, 3]
def baseStart_2484793 : Nat := 118140960795 + 2484793 * 2 ^ 59
def prefixEnd_2484793 : Nat := 4983230072969 + 3 ^ 40 * 2484793 * 2
def baseEnd_2484793 : Nat := 1275893135927401969660151

theorem tailTrace_2484793 : CollatzResearch.WordTrace tailWord_2484793 prefixEnd_2484793 1275893135927401969660151 := by
  unfold tailWord_2484793
  simp only [CollatzResearch.WordTrace]
  refine ⟨90627846087026804703779033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60418564058017869802519355 90627846087026804703779033)
  ·
    refine ⟨67970884565270103527834275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90627846087026804703779033 67970884565270103527834275)
    ·
      refine ⟨101956326847905155291751413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67970884565270103527834275 101956326847905155291751413)
      ·
        refine ⟨9558405641991108308601695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101956326847905155291751413 9558405641991108308601695)
        ·
          refine ⟨14337608462986662462902543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9558405641991108308601695 14337608462986662462902543)
          ·
            refine ⟨21506412694479993694353815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14337608462986662462902543 21506412694479993694353815)
            ·
              refine ⟨32259619041719990541530723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21506412694479993694353815 32259619041719990541530723)
              ·
                refine ⟨48389428562579985812296085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32259619041719990541530723 48389428562579985812296085)
                ·
                  refine ⟨2268254463870936834951379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48389428562579985812296085 2268254463870936834951379)
                  ·
                    refine ⟨3402381695806405252427069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2268254463870936834951379 3402381695806405252427069)
                    ·
                      refine ⟨1275893135927401969660151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3402381695806405252427069 1275893135927401969660151)
                      ·
                        rfl

theorem cell23_2484793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_2484793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484793 prefixEnd_2484793 := by exact prefixLift 2484793
  have htrace : WordTrace (prefixWord ++ tailWord_2484793) baseStart_2484793 baseEnd_2484793 := by
    simpa [prefixWord, tailWord_2484793, baseEnd_2484793] using wordTrace_append hprefix tailTrace_2484793
  have hstable : (prefixWord ++ tailWord_2484793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484793).length < 2 ^ (prefixWord ++ tailWord_2484793).sum := by decide
  have hdescent : baseEnd_2484793 < baseStart_2484793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484794 : List Nat := [3, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2]
def baseStart_2484794 : Nat := 118140960795 + 2484794 * 2 ^ 59
def prefixEnd_2484794 : Nat := 4983230072969 + 3 ^ 40 * 2484794 * 2
def baseEnd_2484794 : Nat := 1275893649408056465747647

theorem tailTrace_2484794 : CollatzResearch.WordTrace tailWord_2484794 prefixEnd_2484794 1275893649408056465747647 := by
  unfold tailWord_2484794
  simp only [CollatzResearch.WordTrace]
  refine ⟨22656970640005795468641359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60418588373348787916376957 22656970640005795468641359)
  ·
    refine ⟨33985455960008693202962039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22656970640005795468641359 33985455960008693202962039)
    ·
      refine ⟨50978183940013039804443059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33985455960008693202962039 50978183940013039804443059)
      ·
        refine ⟨76467275910019559706664589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50978183940013039804443059 76467275910019559706664589)
        ·
          refine ⟨28675228466257334889999221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76467275910019559706664589 28675228466257334889999221)
          ·
            refine ⟨2688302668711625145937427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28675228466257334889999221 2688302668711625145937427)
            ·
              refine ⟨4032454003067437718906141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2688302668711625145937427 4032454003067437718906141)
              ·
                refine ⟨1512170251150289144589803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4032454003067437718906141 1512170251150289144589803)
                ·
                  refine ⟨2268255376725433716884705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512170251150289144589803 2268255376725433716884705)
                  ·
                    refine ⟨1701191532544075287663529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2268255376725433716884705 1701191532544075287663529)
                    ·
                      refine ⟨1275893649408056465747647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1701191532544075287663529 1275893649408056465747647)
                      ·
                        rfl

theorem cell23_2484794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 3, 1, 2, 2].length) (baseStart_2484794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484794 prefixEnd_2484794 := by exact prefixLift 2484794
  have htrace : WordTrace (prefixWord ++ tailWord_2484794) baseStart_2484794 baseEnd_2484794 := by
    simpa [prefixWord, tailWord_2484794, baseEnd_2484794] using wordTrace_append hprefix tailTrace_2484794
  have hstable : (prefixWord ++ tailWord_2484794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484794).length < 2 ^ (prefixWord ++ tailWord_2484794).sum := by decide
  have hdescent : baseEnd_2484794 < baseStart_2484794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484836 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_2484836 : Nat := 118140960795 + 2484836 * 2 ^ 59
def prefixEnd_2484836 : Nat := 4983230072969 + 3 ^ 40 * 2484836 * 2
def baseEnd_2484836 : Nat := 1275915215595545301422453

theorem tailTrace_2484836 : CollatzResearch.WordTrace tailWord_2484836 prefixEnd_2484836 1275915215595545301422453 := by
  unfold tailWord_2484836
  simp only [CollatzResearch.WordTrace]
  refine ⟨45314707212935511523797181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60419609617247348698396241 45314707212935511523797181)
  ·
    refine ⟨16993015204850816821423943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45314707212935511523797181 16993015204850816821423943)
    ·
      refine ⟨25489522807276225232135915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16993015204850816821423943 25489522807276225232135915)
      ·
        refine ⟨38234284210914337848203873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25489522807276225232135915 38234284210914337848203873)
        ·
          refine ⟨28675713158185753386152905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38234284210914337848203873 28675713158185753386152905)
          ·
            refine ⟨21506784868639315039614679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28675713158185753386152905 21506784868639315039614679)
            ·
              refine ⟨32260177302958972559422019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21506784868639315039614679 32260177302958972559422019)
              ·
                refine ⟨48390265954438458839133029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32260177302958972559422019 48390265954438458839133029)
                ·
                  refine ⟨9073174866457211032337443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48390265954438458839133029 9073174866457211032337443)
                  ·
                    refine ⟨13609762299685816548506165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9073174866457211032337443 13609762299685816548506165)
                    ·
                      refine ⟨1275915215595545301422453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13609762299685816548506165 1275915215595545301422453)
                      ·
                        rfl

theorem cell23_2484836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_2484836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484836 prefixEnd_2484836 := by exact prefixLift 2484836
  have htrace : WordTrace (prefixWord ++ tailWord_2484836) baseStart_2484836 baseEnd_2484836 := by
    simpa [prefixWord, tailWord_2484836, baseEnd_2484836] using wordTrace_append hprefix tailTrace_2484836
  have hstable : (prefixWord ++ tailWord_2484836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484836).length < 2 ^ (prefixWord ++ tailWord_2484836).sum := by decide
  have hdescent : baseEnd_2484836 < baseStart_2484836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484884 : List Nat := [2, 4, 2, 2, 1, 1, 2, 3, 2, 2, 2]
def baseStart_2484884 : Nat := 118140960795 + 2484884 * 2 ^ 59
def prefixEnd_2484884 : Nat := 4983230072969 + 3 ^ 40 * 2484884 * 2
def baseEnd_2484884 : Nat := 1275939862666961113622233

theorem tailTrace_2484884 : CollatzResearch.WordTrace tailWord_2484884 prefixEnd_2484884 1275939862666961113622233 := by
  unfold tailWord_2484884
  simp only [CollatzResearch.WordTrace]
  refine ⟨45315582564848563622670853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60420776753131418163561137 45315582564848563622670853)
  ·
    refine ⟨8496671730909105679250785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45315582564848563622670853 8496671730909105679250785)
    ·
      refine ⟨6372503798181829259438089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8496671730909105679250785 6372503798181829259438089)
      ·
        refine ⟨4779377848636371944578567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6372503798181829259438089 4779377848636371944578567)
        ·
          refine ⟨7169066772954557916867851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4779377848636371944578567 7169066772954557916867851)
          ·
            refine ⟨10753600159431836875301777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7169066772954557916867851 10753600159431836875301777)
            ·
              refine ⟨8065200119573877656476333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10753600159431836875301777 8065200119573877656476333)
              ·
                refine ⟨3024450044840204121178625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8065200119573877656476333 3024450044840204121178625)
                ·
                  refine ⟨2268337533630153090883969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3024450044840204121178625 2268337533630153090883969)
                  ·
                    refine ⟨1701253150222614818162977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2268337533630153090883969 1701253150222614818162977)
                    ·
                      refine ⟨1275939862666961113622233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1701253150222614818162977 1275939862666961113622233)
                      ·
                        rfl

theorem cell23_2484884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_2484884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484884 prefixEnd_2484884 := by exact prefixLift 2484884
  have htrace : WordTrace (prefixWord ++ tailWord_2484884) baseStart_2484884 baseEnd_2484884 := by
    simpa [prefixWord, tailWord_2484884, baseEnd_2484884] using wordTrace_append hprefix tailTrace_2484884
  have hstable : (prefixWord ++ tailWord_2484884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484884).length < 2 ^ (prefixWord ++ tailWord_2484884).sum := by decide
  have hdescent : baseEnd_2484884 < baseStart_2484884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484890 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 7]
def baseStart_2484890 : Nat := 118140960795 + 2484890 * 2 ^ 59
def prefixEnd_2484890 : Nat := 4983230072969 + 3 ^ 40 * 2484890 * 2
def baseEnd_2484890 : Nat := 141771438172320898905245

theorem tailTrace_2484890 : CollatzResearch.WordTrace tailWord_2484890 prefixEnd_2484890 141771438172320898905245 := by
  unfold tailWord_2484890
  simp only [CollatzResearch.WordTrace]
  refine ⟨22657845991918847567515031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60420922645116926846706749 22657845991918847567515031)
  ·
    refine ⟨33986768987878271351272547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22657845991918847567515031 33986768987878271351272547)
    ·
      refine ⟨50980153481817407026908821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33986768987878271351272547 50980153481817407026908821)
      ·
        refine ⟨2389694694460190954386351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 50980153481817407026908821 2389694694460190954386351)
        ·
          refine ⟨3584542041690286431579527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2389694694460190954386351 3584542041690286431579527)
          ·
            refine ⟨5376813062535429647369291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3584542041690286431579527 5376813062535429647369291)
            ·
              refine ⟨8065219593803144471053937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5376813062535429647369291 8065219593803144471053937)
              ·
                refine ⟨6048914695352358353290453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8065219593803144471053937 6048914695352358353290453)
                ·
                  refine ⟨141771438172320898905245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6048914695352358353290453 141771438172320898905245)
                  ·
                    rfl

theorem cell23_2484890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 7].length) (baseStart_2484890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484890 prefixEnd_2484890 := by exact prefixLift 2484890
  have htrace : WordTrace (prefixWord ++ tailWord_2484890) baseStart_2484890 baseEnd_2484890 := by
    simpa [prefixWord, tailWord_2484890, baseEnd_2484890] using wordTrace_append hprefix tailTrace_2484890
  have hstable : (prefixWord ++ tailWord_2484890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484890).length < 2 ^ (prefixWord ++ tailWord_2484890).sum := by decide
  have hdescent : baseEnd_2484890 < baseStart_2484890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484918 : List Nat := [5, 1, 3, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_2484918 : Nat := 118140960795 + 2484918 * 2 ^ 59
def prefixEnd_2484918 : Nat := 4983230072969 + 3 ^ 40 * 2484918 * 2
def baseEnd_2484918 : Nat := 1275957321009213980597077

theorem tailTrace_2484918 : CollatzResearch.WordTrace tailWord_2484918 prefixEnd_2484918 1275957321009213980597077 := by
  unfold tailWord_2484918
  simp only [CollatzResearch.WordTrace]
  refine ⟨5664525325723371940754963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60421603474382634034719605 5664525325723371940754963)
  ·
    refine ⟨8496787988585057911132445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5664525325723371940754963 8496787988585057911132445)
    ·
      refine ⟨3186295495719396716674667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8496787988585057911132445 3186295495719396716674667)
      ·
        refine ⟨4779443243579095075012001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3186295495719396716674667 4779443243579095075012001)
        ·
          refine ⟨3584582432684321306259001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4779443243579095075012001 3584582432684321306259001)
          ·
            refine ⟨2688436824513240979694251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3584582432684321306259001 2688436824513240979694251)
            ·
              refine ⟨4032655236769861469541377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2688436824513240979694251 4032655236769861469541377)
              ·
                refine ⟨3024491427577396102156033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4032655236769861469541377 3024491427577396102156033)
                ·
                  refine ⟨2268368570683047076617025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3024491427577396102156033 2268368570683047076617025)
                  ·
                    refine ⟨1701276428012285307462769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2268368570683047076617025 1701276428012285307462769)
                    ·
                      refine ⟨1275957321009213980597077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1701276428012285307462769 1275957321009213980597077)
                      ·
                        rfl

theorem cell23_2484918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_2484918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484918 prefixEnd_2484918 := by exact prefixLift 2484918
  have htrace : WordTrace (prefixWord ++ tailWord_2484918) baseStart_2484918 baseEnd_2484918 := by
    simpa [prefixWord, tailWord_2484918, baseEnd_2484918] using wordTrace_append hprefix tailTrace_2484918
  have hstable : (prefixWord ++ tailWord_2484918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484918).length < 2 ^ (prefixWord ++ tailWord_2484918).sum := by decide
  have hdescent : baseEnd_2484918 < baseStart_2484918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484963 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 8]
def baseStart_2484963 : Nat := 118140960795 + 2484963 * 2 ^ 59
def prefixEnd_2484963 : Nat := 4983230072969 + 3 ^ 40 * 2484963 * 2
def baseEnd_2484963 : Nat := 141775603070962922726041

theorem tailTrace_2484963 : CollatzResearch.WordTrace tailWord_2484963 prefixEnd_2484963 141775603070962922726041 := by
  unfold tailWord_2484963
  simp only [CollatzResearch.WordTrace]
  refine ⟨90634046496410923737467543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60422697664273949158311695 90634046496410923737467543)
  ·
    refine ⟨135951069744616385606201315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90634046496410923737467543 135951069744616385606201315)
    ·
      refine ⟨203926604616924578409301973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135951069744616385606201315 203926604616924578409301973)
      ·
        refine ⟨4779529795709169806468015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 203926604616924578409301973 4779529795709169806468015)
        ·
          refine ⟨7169294693563754709702023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4779529795709169806468015 7169294693563754709702023)
          ·
            refine ⟨10753942040345632064553035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7169294693563754709702023 10753942040345632064553035)
            ·
              refine ⟨16130913060518448096829553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10753942040345632064553035 16130913060518448096829553)
              ·
                refine ⟨12098184795388836072622165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16130913060518448096829553 12098184795388836072622165)
                ·
                  refine ⟨141775603070962922726041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12098184795388836072622165 141775603070962922726041)
                  ·
                    rfl

theorem cell23_2484963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 8].length) (baseStart_2484963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484963 prefixEnd_2484963 := by exact prefixLift 2484963
  have htrace : WordTrace (prefixWord ++ tailWord_2484963) baseStart_2484963 baseEnd_2484963 := by
    simpa [prefixWord, tailWord_2484963, baseEnd_2484963] using wordTrace_append hprefix tailTrace_2484963
  have hstable : (prefixWord ++ tailWord_2484963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484963).length < 2 ^ (prefixWord ++ tailWord_2484963).sum := by decide
  have hdescent : baseEnd_2484963 < baseStart_2484963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2484993 : List Nat := [1, 2, 4, 1, 1, 1, 1, 4, 3, 5]
def baseStart_2484993 : Nat := 118140960795 + 2484993 * 2 ^ 59
def prefixEnd_2484993 : Nat := 4983230072969 + 3 ^ 40 * 2484993 * 2
def baseEnd_2484993 : Nat := 425331944019433729053077

theorem tailTrace_2484993 : CollatzResearch.WordTrace tailWord_2484993 prefixEnd_2484993 425331944019433729053077 := by
  unfold tailWord_2484993
  simp only [CollatzResearch.WordTrace]
  refine ⟨90635140686302238861059633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60423427124201492574039755 90635140686302238861059633)
  ·
    refine ⟨67976355514726679145794725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90635140686302238861059633 67976355514726679145794725)
    ·
      refine ⟨12745566659011252339836511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67976355514726679145794725 12745566659011252339836511)
      ·
        refine ⟨19118349988516878509754767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12745566659011252339836511 19118349988516878509754767)
        ·
          refine ⟨28677524982775317764632151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19118349988516878509754767 28677524982775317764632151)
          ·
            refine ⟨43016287474162976646948227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28677524982775317764632151 43016287474162976646948227)
            ·
              refine ⟨64524431211244464970422341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43016287474162976646948227 64524431211244464970422341)
              ·
                refine ⟨12098330852108337181954189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64524431211244464970422341 12098330852108337181954189)
                ·
                  refine ⟨4536874069540626443232821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12098330852108337181954189 4536874069540626443232821)
                  ·
                    refine ⟨425331944019433729053077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4536874069540626443232821 425331944019433729053077)
                    ·
                      rfl

theorem cell23_2484993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_2484993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2484993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2484993 prefixEnd_2484993 := by exact prefixLift 2484993
  have htrace : WordTrace (prefixWord ++ tailWord_2484993) baseStart_2484993 baseEnd_2484993 := by
    simpa [prefixWord, tailWord_2484993, baseEnd_2484993] using wordTrace_append hprefix tailTrace_2484993
  have hstable : (prefixWord ++ tailWord_2484993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2484993).length < 2 ^ (prefixWord ++ tailWord_2484993).sum := by decide
  have hdescent : baseEnd_2484993 < baseStart_2484993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2484993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485023 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 3, 6]
def baseStart_2485023 : Nat := 118140960795 + 2485023 * 2 ^ 59
def prefixEnd_2485023 : Nat := 4983230072969 + 3 ^ 40 * 2485023 * 2
def baseEnd_2485023 : Nat := 425337078825978689928031

theorem tailTrace_2485023 : CollatzResearch.WordTrace tailWord_2485023 prefixEnd_2485023 425337078825978689928031 := by
  unfold tailWord_2485023
  simp only [CollatzResearch.WordTrace]
  refine ⟨90636234876193553984651723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60424156584129035989767815 90636234876193553984651723)
  ·
    refine ⟨135954352314290330976977585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90636234876193553984651723 135954352314290330976977585)
    ·
      refine ⟨101965764235717748232733189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135954352314290330976977585 101965764235717748232733189)
      ·
        refine ⟨19118580794197077793637473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101965764235717748232733189 19118580794197077793637473)
        ·
          refine ⟨14338935595647808345228105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19118580794197077793637473 14338935595647808345228105)
          ·
            refine ⟨10754201696735856258921079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14338935595647808345228105 10754201696735856258921079)
            ·
              refine ⟨16131302545103784388381619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10754201696735856258921079 16131302545103784388381619)
              ·
                refine ⟨24196953817655676582572429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16131302545103784388381619 24196953817655676582572429)
                ·
                  refine ⟨9073857681620878718464661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24196953817655676582572429 9073857681620878718464661)
                  ·
                    refine ⟨425337078825978689928031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9073857681620878718464661 425337078825978689928031)
                    ·
                      rfl

theorem cell23_2485023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 6].length) (baseStart_2485023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485023 prefixEnd_2485023 := by exact prefixLift 2485023
  have htrace : WordTrace (prefixWord ++ tailWord_2485023) baseStart_2485023 baseEnd_2485023 := by
    simpa [prefixWord, tailWord_2485023, baseEnd_2485023] using wordTrace_append hprefix tailTrace_2485023
  have hstable : (prefixWord ++ tailWord_2485023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485023).length < 2 ^ (prefixWord ++ tailWord_2485023).sum := by decide
  have hdescent : baseEnd_2485023 < baseStart_2485023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485047 : List Nat := [1, 1, 3, 1, 2, 1, 4, 3, 3, 2, 2]
def baseStart_2485047 : Nat := 118140960795 + 2485047 * 2 ^ 59
def prefixEnd_2485047 : Nat := 4983230072969 + 3 ^ 40 * 2485047 * 2
def baseEnd_2485047 : Nat := 1276023560013643975883983

theorem tailTrace_2485047 : CollatzResearch.WordTrace tailWord_2485047 prefixEnd_2485047 1276023560013643975883983 := by
  unfold tailWord_2485047
  simp only [CollatzResearch.WordTrace]
  refine ⟨90637110228106606083525395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60424740152071070722350263 90637110228106606083525395)
  ·
    refine ⟨135955665342159909125288093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90637110228106606083525395 135955665342159909125288093)
    ·
      refine ⟨50983374503309965921983035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135955665342159909125288093 50983374503309965921983035)
      ·
        refine ⟨76475061754964948882974553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50983374503309965921983035 76475061754964948882974553)
        ·
          refine ⟨57356296316223711662230915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76475061754964948882974553 57356296316223711662230915)
          ·
            refine ⟨86034444474335567493346373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57356296316223711662230915 86034444474335567493346373)
            ·
              refine ⟨16131458338937918905002445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86034444474335567493346373 16131458338937918905002445)
              ·
                refine ⟨6049296877101719589375917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16131458338937918905002445 6049296877101719589375917)
                ·
                  refine ⟨2268486328913144846015969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6049296877101719589375917 2268486328913144846015969)
                  ·
                    refine ⟨1701364746684858634511977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2268486328913144846015969 1701364746684858634511977)
                    ·
                      refine ⟨1276023560013643975883983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1701364746684858634511977 1276023560013643975883983)
                      ·
                        rfl

theorem cell23_2485047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 2, 2].length) (baseStart_2485047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485047 prefixEnd_2485047 := by exact prefixLift 2485047
  have htrace : WordTrace (prefixWord ++ tailWord_2485047) baseStart_2485047 baseEnd_2485047 := by
    simpa [prefixWord, tailWord_2485047, baseEnd_2485047] using wordTrace_append hprefix tailTrace_2485047
  have hstable : (prefixWord ++ tailWord_2485047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485047).length < 2 ^ (prefixWord ++ tailWord_2485047).sum := by decide
  have hdescent : baseEnd_2485047 < baseStart_2485047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485081 : List Nat := [1, 2, 1, 2, 2, 5, 2, 3, 1, 2, 2]
def baseStart_2485081 : Nat := 118140960795 + 2485081 * 2 ^ 59
def prefixEnd_2485081 : Nat := 4983230072969 + 3 ^ 40 * 2485081 * 2
def baseEnd_2485081 : Nat := 1276041018355896842858827

theorem tailTrace_2485081 : CollatzResearch.WordTrace tailWord_2485081 prefixEnd_2485081 1276041018355896842858827 := by
  unfold tailWord_2485081
  simp only [CollatzResearch.WordTrace]
  refine ⟨90638350309983429890263097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60425566873322286593508731 90638350309983429890263097)
  ·
    refine ⟨67978762732487572417697323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90638350309983429890263097 67978762732487572417697323)
    ·
      refine ⟨101968144098731358626545985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67978762732487572417697323 101968144098731358626545985)
      ·
        refine ⟨76476108074048518969909489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101968144098731358626545985 76476108074048518969909489)
        ·
          refine ⟨57357081055536389227432117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76476108074048518969909489 57357081055536389227432117)
          ·
            refine ⟨5377226348956536490071761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57357081055536389227432117 5377226348956536490071761)
            ·
              refine ⟨4032919761717402367553821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5377226348956536490071761 4032919761717402367553821)
              ·
                refine ⟨1512344910644025887832683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4032919761717402367553821 1512344910644025887832683)
                ·
                  refine ⟨2268517365966038831749025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512344910644025887832683 2268517365966038831749025)
                  ·
                    refine ⟨1701388024474529123811769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2268517365966038831749025 1701388024474529123811769)
                    ·
                      refine ⟨1276041018355896842858827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1701388024474529123811769 1276041018355896842858827)
                      ·
                        rfl

theorem cell23_2485081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3, 1, 2, 2].length) (baseStart_2485081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485081 prefixEnd_2485081 := by exact prefixLift 2485081
  have htrace : WordTrace (prefixWord ++ tailWord_2485081) baseStart_2485081 baseEnd_2485081 := by
    simpa [prefixWord, tailWord_2485081, baseEnd_2485081] using wordTrace_append hprefix tailTrace_2485081
  have hstable : (prefixWord ++ tailWord_2485081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485081).length < 2 ^ (prefixWord ++ tailWord_2485081).sum := by decide
  have hdescent : baseEnd_2485081 < baseStart_2485081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485084 : List Nat := [2, 2, 4, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_2485084 : Nat := 118140960795 + 2485084 * 2 ^ 59
def prefixEnd_2485084 : Nat := 4983230072969 + 3 ^ 40 * 2485084 * 2
def baseEnd_2485084 : Nat := 1276042558797860331121313

theorem tailTrace_2485084 : CollatzResearch.WordTrace tailWord_2485084 prefixEnd_2485084 1276042558797860331121313 := by
  unfold tailWord_2485084
  simp only [CollatzResearch.WordTrace]
  refine ⟨45319229864486280701311153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60425639819315040935081537 45319229864486280701311153)
  ·
    refine ⟨33989422398364710525983365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45319229864486280701311153 33989422398364710525983365)
    ·
      refine ⟨6373016699693383223621881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33989422398364710525983365 6373016699693383223621881)
      ·
        refine ⟨4779762524770037417716411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6373016699693383223621881 4779762524770037417716411)
        ·
          refine ⟨7169643787155056126574617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4779762524770037417716411 7169643787155056126574617)
          ·
            refine ⟨5377232840366292094930963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7169643787155056126574617 5377232840366292094930963)
            ·
              refine ⟨8065849260549438142396445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5377232840366292094930963 8065849260549438142396445)
              ·
                refine ⟨3024693472706039303398667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8065849260549438142396445 3024693472706039303398667)
                ·
                  refine ⟨4537040209059058955098001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3024693472706039303398667 4537040209059058955098001)
                  ·
                    refine ⟨3402780156794294216323501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4537040209059058955098001 3402780156794294216323501)
                    ·
                      refine ⟨1276042558797860331121313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3402780156794294216323501 1276042558797860331121313)
                      ·
                        rfl

theorem cell23_2485084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_2485084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485084 prefixEnd_2485084 := by exact prefixLift 2485084
  have htrace : WordTrace (prefixWord ++ tailWord_2485084) baseStart_2485084 baseEnd_2485084 := by
    simpa [prefixWord, tailWord_2485084, baseEnd_2485084] using wordTrace_append hprefix tailTrace_2485084
  have hstable : (prefixWord ++ tailWord_2485084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485084).length < 2 ^ (prefixWord ++ tailWord_2485084).sum := by decide
  have hdescent : baseEnd_2485084 < baseStart_2485084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485103 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 4]
def baseStart_2485103 : Nat := 118140960795 + 2485103 * 2 ^ 59
def prefixEnd_2485103 : Nat := 4983230072969 + 3 ^ 40 * 2485103 * 2
def baseEnd_2485103 : Nat := 1276052314930295756783725

theorem tailTrace_2485103 : CollatzResearch.WordTrace tailWord_2485103 prefixEnd_2485103 1276052314930295756783725 := by
  unfold tailWord_2485103
  simp only [CollatzResearch.WordTrace]
  refine ⟨90639152715903727647563963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60426101810602485098375975 90639152715903727647563963)
  ·
    refine ⟨135958729073855591471345945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90639152715903727647563963 135958729073855591471345945)
    ·
      refine ⟨101969046805391693603509459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135958729073855591471345945 101969046805391693603509459)
      ·
        refine ⟨152953570208087540405264189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101969046805391693603509459 152953570208087540405264189)
        ·
          refine ⟨57357588828032827651974071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152953570208087540405264189 57357588828032827651974071)
          ·
            refine ⟨86036383242049241477961107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57357588828032827651974071 86036383242049241477961107)
            ·
              refine ⟨129054574863073862216941661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86036383242049241477961107 129054574863073862216941661)
              ·
                refine ⟨48395465573652698331353123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129054574863073862216941661 48395465573652698331353123)
                ·
                  refine ⟨72593198360479047497029685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48395465573652698331353123 72593198360479047497029685)
                  ·
                    refine ⟨6805612346294910702846533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72593198360479047497029685 6805612346294910702846533)
                    ·
                      refine ⟨1276052314930295756783725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6805612346294910702846533 1276052314930295756783725)
                      ·
                        rfl

theorem cell23_2485103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_2485103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485103 prefixEnd_2485103 := by exact prefixLift 2485103
  have htrace : WordTrace (prefixWord ++ tailWord_2485103) baseStart_2485103 baseEnd_2485103 := by
    simpa [prefixWord, tailWord_2485103, baseEnd_2485103] using wordTrace_append hprefix tailTrace_2485103
  have hstable : (prefixWord ++ tailWord_2485103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485103).length < 2 ^ (prefixWord ++ tailWord_2485103).sum := by decide
  have hdescent : baseEnd_2485103 < baseStart_2485103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485165 : List Nat := [1, 5, 2, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_2485165 : Nat := 118140960795 + 2485165 * 2 ^ 59
def prefixEnd_2485165 : Nat := 4983230072969 + 3 ^ 40 * 2485165 * 2
def baseEnd_2485165 : Nat := 1276084150730874514208441

theorem tailTrace_2485165 : CollatzResearch.WordTrace tailWord_2485165 prefixEnd_2485165 1276084150730874514208441 := by
  unfold tailWord_2485165
  simp only [CollatzResearch.WordTrace]
  refine ⟨90641414041679112236320949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60427609361119408157547299 90641414041679112236320949)
  ·
    refine ⟨8497632566407416772155089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90641414041679112236320949 8497632566407416772155089)
    ·
      refine ⟨6373224424805562579116317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8497632566407416772155089 6373224424805562579116317)
      ·
        refine ⟨2389959159302085967168619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6373224424805562579116317 2389959159302085967168619)
        ·
          refine ⟨3584938738953128950752929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2389959159302085967168619 3584938738953128950752929)
          ·
            refine ⟨2688704054214846713064697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3584938738953128950752929 2688704054214846713064697)
            ·
              refine ⟨2016528040661135034798523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2688704054214846713064697 2016528040661135034798523)
              ·
                refine ⟨3024792060991702552197785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2016528040661135034798523 3024792060991702552197785)
                ·
                  refine ⟨2268594045743776914148339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3024792060991702552197785 2268594045743776914148339)
                  ·
                    refine ⟨3402891068615665371222509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2268594045743776914148339 3402891068615665371222509)
                    ·
                      refine ⟨1276084150730874514208441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3402891068615665371222509 1276084150730874514208441)
                      ·
                        rfl

theorem cell23_2485165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_2485165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485165 prefixEnd_2485165 := by exact prefixLift 2485165
  have htrace : WordTrace (prefixWord ++ tailWord_2485165) baseStart_2485165 baseEnd_2485165 := by
    simpa [prefixWord, tailWord_2485165, baseEnd_2485165] using wordTrace_append hprefix tailTrace_2485165
  have hstable : (prefixWord ++ tailWord_2485165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485165).length < 2 ^ (prefixWord ++ tailWord_2485165).sum := by decide
  have hdescent : baseEnd_2485165 < baseStart_2485165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485244 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 2, 1, 4]
def baseStart_2485244 : Nat := 118140960795 + 2485244 * 2 ^ 59
def prefixEnd_2485244 : Nat := 4983230072969 + 3 ^ 40 * 2485244 * 2
def baseEnd_2485244 : Nat := 1276124715702579705120577

theorem tailTrace_2485244 : CollatzResearch.WordTrace tailWord_2485244 prefixEnd_2485244 1276124715702579705120577 := by
  unfold tailWord_2485244
  simp only [CollatzResearch.WordTrace]
  refine ⟨45322147704196454364223393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60429530272261939152297857 45322147704196454364223393)
  ·
    refine ⟨33991610778147340773167545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45322147704196454364223393 33991610778147340773167545)
    ·
      refine ⟨25493708083610505579875659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33991610778147340773167545 25493708083610505579875659)
      ·
        refine ⟨38240562125415758369813489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25493708083610505579875659 38240562125415758369813489)
        ·
          refine ⟨28680421594061818777360117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38240562125415758369813489 28680421594061818777360117)
          ·
            refine ⟨2688789524443295510377511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28680421594061818777360117 2688789524443295510377511)
            ·
              refine ⟨4033184286664943265566267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2688789524443295510377511 4033184286664943265566267)
              ·
                refine ⟨6049776429997414898349401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4033184286664943265566267 6049776429997414898349401)
                ·
                  refine ⟨4537332322498061173762051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6049776429997414898349401 4537332322498061173762051)
                  ·
                    refine ⟨6805998483747091760643077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4537332322498061173762051 6805998483747091760643077)
                    ·
                      refine ⟨1276124715702579705120577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6805998483747091760643077 1276124715702579705120577)
                      ·
                        rfl

theorem cell23_2485244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_2485244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485244 prefixEnd_2485244 := by exact prefixLift 2485244
  have htrace : WordTrace (prefixWord ++ tailWord_2485244) baseStart_2485244 baseEnd_2485244 := by
    simpa [prefixWord, tailWord_2485244, baseEnd_2485244] using wordTrace_append hprefix tailTrace_2485244
  have hstable : (prefixWord ++ tailWord_2485244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485244).length < 2 ^ (prefixWord ++ tailWord_2485244).sum := by decide
  have hdescent : baseEnd_2485244 < baseStart_2485244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485271 : List Nat := [1, 1, 3, 5, 1, 1, 2, 4, 1, 4]
def baseStart_2485271 : Nat := 118140960795 + 2485271 * 2 ^ 59
def prefixEnd_2485271 : Nat := 4983230072969 + 3 ^ 40 * 2485271 * 2
def baseEnd_2485271 : Nat := 425379526560083699827651

theorem tailTrace_2485271 : CollatzResearch.WordTrace tailWord_2485271 prefixEnd_2485271 425379526560083699827651 := by
  unfold tailWord_2485271
  simp only [CollatzResearch.WordTrace]
  refine ⟨90645280179295092339679667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60430186786196728226453111 90645280179295092339679667)
  ·
    refine ⟨135967920268942638509519501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90645280179295092339679667 135967920268942638509519501)
    ·
      refine ⟨50987970100853489441069813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135967920268942638509519501 50987970100853489441069813)
      ·
        refine ⟨4780122196955014635100295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50987970100853489441069813 4780122196955014635100295)
        ·
          refine ⟨7170183295432521952650443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4780122196955014635100295 7170183295432521952650443)
          ·
            refine ⟨10755274943148782928975665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7170183295432521952650443 10755274943148782928975665)
            ·
              refine ⟨8066456207361587196731749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10755274943148782928975665 8066456207361587196731749)
              ·
                refine ⟨1512460538880297599387203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8066456207361587196731749 1512460538880297599387203)
                ·
                  refine ⟨2268690808320446399080805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512460538880297599387203 2268690808320446399080805)
                  ·
                    refine ⟨425379526560083699827651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2268690808320446399080805 425379526560083699827651)
                    ·
                      rfl

theorem cell23_2485271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 4, 1, 4].length) (baseStart_2485271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485271 prefixEnd_2485271 := by exact prefixLift 2485271
  have htrace : WordTrace (prefixWord ++ tailWord_2485271) baseStart_2485271 baseEnd_2485271 := by
    simpa [prefixWord, tailWord_2485271, baseEnd_2485271] using wordTrace_append hprefix tailTrace_2485271
  have hstable : (prefixWord ++ tailWord_2485271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485271).length < 2 ^ (prefixWord ++ tailWord_2485271).sum := by decide
  have hdescent : baseEnd_2485271 < baseStart_2485271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485304 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 1, 5, 2]
def baseStart_2485304 : Nat := 118140960795 + 2485304 * 2 ^ 59
def prefixEnd_2485304 : Nat := 4983230072969 + 3 ^ 40 * 2485304 * 2
def baseEnd_2485304 : Nat := 1276155524541849470370301

theorem tailTrace_2485304 : CollatzResearch.WordTrace tailWord_2485304 prefixEnd_2485304 1276155524541849470370301 := by
  unfold tailWord_2485304
  simp only [CollatzResearch.WordTrace]
  refine ⟨45323241894087769487815483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60430989192117025983753977 45323241894087769487815483)
  ·
    refine ⟨67984862841131654231723225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45323241894087769487815483 67984862841131654231723225)
    ·
      refine ⟨50988647130848740673792419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67984862841131654231723225 50988647130848740673792419)
      ·
        refine ⟨76482970696273111010688629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50988647130848740673792419 76482970696273111010688629)
        ·
          refine ⟨7170278502775604157252059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76482970696273111010688629 7170278502775604157252059)
          ·
            refine ⟨10755417754163406235878089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7170278502775604157252059 10755417754163406235878089)
            ·
              refine ⟨8066563315622554676908567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10755417754163406235878089 8066563315622554676908567)
              ·
                refine ⟨12099844973433832015362851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8066563315622554676908567 12099844973433832015362851)
                ·
                  refine ⟨18149767460150748023044277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12099844973433832015362851 18149767460150748023044277)
                  ·
                    refine ⟨1701540699389132627160401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18149767460150748023044277 1701540699389132627160401)
                    ·
                      refine ⟨1276155524541849470370301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1701540699389132627160401 1276155524541849470370301)
                      ·
                        rfl

theorem cell23_2485304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 1, 5, 2].length) (baseStart_2485304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485304 prefixEnd_2485304 := by exact prefixLift 2485304
  have htrace : WordTrace (prefixWord ++ tailWord_2485304) baseStart_2485304 baseEnd_2485304 := by
    simpa [prefixWord, tailWord_2485304, baseEnd_2485304] using wordTrace_append hprefix tailTrace_2485304
  have hstable : (prefixWord ++ tailWord_2485304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485304).length < 2 ^ (prefixWord ++ tailWord_2485304).sum := by decide
  have hdescent : baseEnd_2485304 < baseStart_2485304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485344 : List Nat := [2, 1, 1, 3, 2, 2, 3, 3, 2, 4]
def baseStart_2485344 : Nat := 118140960795 + 2485344 * 2 ^ 59
def prefixEnd_2485344 : Nat := 4983230072969 + 3 ^ 40 * 2485344 * 2
def baseEnd_2485344 : Nat := 425392021256009771290039

theorem tailTrace_2485344 : CollatzResearch.WordTrace tailWord_2485344 prefixEnd_2485344 425392021256009771290039 := by
  unfold tailWord_2485344
  simp only [CollatzResearch.WordTrace]
  refine ⟨45323971354015312903543543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60431961805353750538058057 45323971354015312903543543)
  ·
    refine ⟨67985957031022969355315315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45323971354015312903543543 67985957031022969355315315)
    ·
      refine ⟨101978935546534454032972973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67985957031022969355315315 101978935546534454032972973)
      ·
        refine ⟨38242100829950420262364865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101978935546534454032972973 38242100829950420262364865)
        ·
          refine ⟨28681575622462815196773649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38242100829950420262364865 28681575622462815196773649)
          ·
            refine ⟨21511181716847111397580237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28681575622462815196773649 21511181716847111397580237)
            ·
              refine ⟨8066693143817666774092589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21511181716847111397580237 8066693143817666774092589)
              ·
                refine ⟨3025009928931625040284721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8066693143817666774092589 3025009928931625040284721)
                ·
                  refine ⟨2268757446698718780213541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3025009928931625040284721 2268757446698718780213541)
                  ·
                    refine ⟨425392021256009771290039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2268757446698718780213541 425392021256009771290039)
                    ·
                      rfl

theorem cell23_2485344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 3, 2, 4].length) (baseStart_2485344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485344 prefixEnd_2485344 := by exact prefixLift 2485344
  have htrace : WordTrace (prefixWord ++ tailWord_2485344) baseStart_2485344 baseEnd_2485344 := by
    simpa [prefixWord, tailWord_2485344, baseEnd_2485344] using wordTrace_append hprefix tailTrace_2485344
  have hstable : (prefixWord ++ tailWord_2485344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485344).length < 2 ^ (prefixWord ++ tailWord_2485344).sum := by decide
  have hdescent : baseEnd_2485344 < baseStart_2485344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485347 : List Nat := [1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 4]
def baseStart_2485347 : Nat := 118140960795 + 2485347 * 2 ^ 59
def prefixEnd_2485347 : Nat := 4983230072969 + 3 ^ 40 * 2485347 * 2
def baseEnd_2485347 : Nat := 1276177604209992802132603

theorem tailTrace_2485347 : CollatzResearch.WordTrace tailWord_2485347 prefixEnd_2485347 1276177604209992802132603 := by
  unfold tailWord_2485347
  simp only [CollatzResearch.WordTrace]
  refine ⟨90648052127019757319446295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60432034751346504879630863 90648052127019757319446295)
  ·
    refine ⟨135972078190529635979169443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90648052127019757319446295 135972078190529635979169443)
    ·
      refine ⟨203958117285794453968754165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135972078190529635979169443 203958117285794453968754165)
      ·
        refine ⟨19121073495543230059570703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203958117285794453968754165 19121073495543230059570703)
        ·
          refine ⟨28681610243314845089356055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19121073495543230059570703 28681610243314845089356055)
          ·
            refine ⟨43022415364972267634034083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28681610243314845089356055 43022415364972267634034083)
            ·
              refine ⟨64533623047458401451051125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43022415364972267634034083 64533623047458401451051125)
              ·
                refine ⟨6050027160699225136036043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64533623047458401451051125 6050027160699225136036043)
                ·
                  refine ⟨9075040741048837704054065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6050027160699225136036043 9075040741048837704054065)
                  ·
                    refine ⟨6806280555786628278040549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9075040741048837704054065 6806280555786628278040549)
                    ·
                      refine ⟨1276177604209992802132603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6806280555786628278040549 1276177604209992802132603)
                      ·
                        rfl

theorem cell23_2485347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_2485347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485347 prefixEnd_2485347 := by exact prefixLift 2485347
  have htrace : WordTrace (prefixWord ++ tailWord_2485347) baseStart_2485347 baseEnd_2485347 := by
    simpa [prefixWord, tailWord_2485347, baseEnd_2485347] using wordTrace_append hprefix tailTrace_2485347
  have hstable : (prefixWord ++ tailWord_2485347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485347).length < 2 ^ (prefixWord ++ tailWord_2485347).sum := by decide
  have hdescent : baseEnd_2485347 < baseStart_2485347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485351 : List Nat := [1, 1, 5, 1, 1, 5, 1, 2, 1, 1, 4]
def baseStart_2485351 : Nat := 118140960795 + 2485351 * 2 ^ 59
def prefixEnd_2485351 : Nat := 4983230072969 + 3 ^ 40 * 2485351 * 2
def baseEnd_2485351 : Nat := 1276179658132610786482585

theorem tailTrace_2485351 : CollatzResearch.WordTrace tailWord_2485351 prefixEnd_2485351 1276179658132610786482585 := by
  unfold tailWord_2485351
  simp only [CollatzResearch.WordTrace]
  refine ⟨90648198019005266002591907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60432132012670177335061271 90648198019005266002591907)
  ·
    refine ⟨135972297028507899003887861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90648198019005266002591907 135972297028507899003887861)
    ·
      refine ⟨12747402846422615531614487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135972297028507899003887861 12747402846422615531614487)
      ·
        refine ⟨19121104269633923297421731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12747402846422615531614487 19121104269633923297421731)
        ·
          refine ⟨28681656404450884946132597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19121104269633923297421731 28681656404450884946132597)
          ·
            refine ⟨2688905287917270463699931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28681656404450884946132597 2688905287917270463699931)
            ·
              refine ⟨4033357931875905695549897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2688905287917270463699931 4033357931875905695549897)
              ·
                refine ⟨3025018448906929271662423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4033357931875905695549897 3025018448906929271662423)
                ·
                  refine ⟨4537527673360393907493635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3025018448906929271662423 4537527673360393907493635)
                  ·
                    refine ⟨6806291510040590861240453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4537527673360393907493635 6806291510040590861240453)
                    ·
                      refine ⟨1276179658132610786482585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6806291510040590861240453 1276179658132610786482585)
                      ·
                        rfl

theorem cell23_2485351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_2485351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485351 prefixEnd_2485351 := by exact prefixLift 2485351
  have htrace : WordTrace (prefixWord ++ tailWord_2485351) baseStart_2485351 baseEnd_2485351 := by
    simpa [prefixWord, tailWord_2485351, baseEnd_2485351] using wordTrace_append hprefix tailTrace_2485351
  have hstable : (prefixWord ++ tailWord_2485351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485351).length < 2 ^ (prefixWord ++ tailWord_2485351).sum := by decide
  have hdescent : baseEnd_2485351 < baseStart_2485351 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485357 : List Nat := [1, 5, 1, 1, 2, 2, 2, 9]
def baseStart_2485357 : Nat := 118140960795 + 2485357 * 2 ^ 59
def prefixEnd_2485357 : Nat := 4983230072969 + 3 ^ 40 * 2485357 * 2
def baseEnd_2485357 : Nat := 47266027370982880111391

theorem tailTrace_2485357 : CollatzResearch.WordTrace tailWord_2485357 prefixEnd_2485357 47266027370982880111391 := by
  unfold tailWord_2485357
  simp only [CollatzResearch.WordTrace]
  refine ⟨90648416856983529027310325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60432277904655686018206883 90648416856983529027310325)
  ·
    refine ⟨8498289080342205846310343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90648416856983529027310325 8498289080342205846310343)
    ·
      refine ⟨12747433620513308769465515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8498289080342205846310343 12747433620513308769465515)
      ·
        refine ⟨19121150430769963154198273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12747433620513308769465515 19121150430769963154198273)
        ·
          refine ⟨14340862823077472365648705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19121150430769963154198273 14340862823077472365648705)
          ·
            refine ⟨10755647117308104274236529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14340862823077472365648705 10755647117308104274236529)
            ·
              refine ⟨8066735337981078205677397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10755647117308104274236529 8066735337981078205677397)
              ·
                refine ⟨47266027370982880111391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8066735337981078205677397 47266027370982880111391)
                ·
                  rfl

theorem cell23_2485357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 9].length) (baseStart_2485357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485357 prefixEnd_2485357 := by exact prefixLift 2485357
  have htrace : WordTrace (prefixWord ++ tailWord_2485357) baseStart_2485357 baseEnd_2485357 := by
    simpa [prefixWord, tailWord_2485357, baseEnd_2485357] using wordTrace_append hprefix tailTrace_2485357
  have hstable : (prefixWord ++ tailWord_2485357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485357).length < 2 ^ (prefixWord ++ tailWord_2485357).sum := by decide
  have hdescent : baseEnd_2485357 < baseStart_2485357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485385 : List Nat := [1, 2, 1, 1, 4, 3, 4, 2, 1, 2, 2]
def baseStart_2485385 : Nat := 118140960795 + 2485385 * 2 ^ 59
def prefixEnd_2485385 : Nat := 4983230072969 + 3 ^ 40 * 2485385 * 2
def baseEnd_2485385 : Nat := 1276197116474863653457429

theorem tailTrace_2485385 : CollatzResearch.WordTrace tailWord_2485385 prefixEnd_2485385 1276197116474863653457429 := by
  unfold tailWord_2485385
  simp only [CollatzResearch.WordTrace]
  refine ⟨90649438100882089809329609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60432958733921393206219739 90649438100882089809329609)
  ·
    refine ⟨67987078575661567356997207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90649438100882089809329609 67987078575661567356997207)
    ·
      refine ⟨101980617863492351035495811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67987078575661567356997207 101980617863492351035495811)
      ·
        refine ⟨152970926795238526553243717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101980617863492351035495811 152970926795238526553243717)
        ·
          refine ⟨28682048774107223728733197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152970926795238526553243717 28682048774107223728733197)
          ·
            refine ⟨10755768290290208898274949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28682048774107223728733197 10755768290290208898274949)
            ·
              refine ⟨2016706554429414168426553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10755768290290208898274949 2016706554429414168426553)
              ·
                refine ⟨1512529915822060626319915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2016706554429414168426553 1512529915822060626319915)
                ·
                  refine ⟨2268794873733090939479873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512529915822060626319915 2268794873733090939479873)
                  ·
                    refine ⟨1701596155299818204609905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2268794873733090939479873 1701596155299818204609905)
                    ·
                      refine ⟨1276197116474863653457429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1701596155299818204609905 1276197116474863653457429)
                      ·
                        rfl

theorem cell23_2485385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 2, 1, 2, 2].length) (baseStart_2485385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485385 prefixEnd_2485385 := by exact prefixLift 2485385
  have htrace : WordTrace (prefixWord ++ tailWord_2485385) baseStart_2485385 baseEnd_2485385 := by
    simpa [prefixWord, tailWord_2485385, baseEnd_2485385] using wordTrace_append hprefix tailTrace_2485385
  have hstable : (prefixWord ++ tailWord_2485385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485385).length < 2 ^ (prefixWord ++ tailWord_2485385).sum := by decide
  have hdescent : baseEnd_2485385 < baseStart_2485385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485427 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 5]
def baseStart_2485427 : Nat := 118140960795 + 2485427 * 2 ^ 59
def prefixEnd_2485427 : Nat := 4983230072969 + 3 ^ 40 * 2485427 * 2
def baseEnd_2485427 : Nat := 1276218682662352489132235

theorem tailTrace_2485427 : CollatzResearch.WordTrace tailWord_2485427 prefixEnd_2485427 1276218682662352489132235 := by
  unfold tailWord_2485427
  simp only [CollatzResearch.WordTrace]
  refine ⟨90650969966729930982358535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60433979977819953988239023 90650969966729930982358535)
  ·
    refine ⟨135976454950094896473537803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90650969966729930982358535 135976454950094896473537803)
    ·
      refine ⟨203964682425142344710306705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135976454950094896473537803 203964682425142344710306705)
      ·
        refine ⟨152973511818856758532730029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203964682425142344710306705 152973511818856758532730029)
        ·
          refine ⟨57365066932071284449773761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152973511818856758532730029 57365066932071284449773761)
          ·
            refine ⟨43023800199053463337330321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57365066932071284449773761 43023800199053463337330321)
            ·
              refine ⟨32267850149290097502997741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43023800199053463337330321 32267850149290097502997741)
              ·
                refine ⟨12100443805983786563624153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32267850149290097502997741 12100443805983786563624153)
                ·
                  refine ⟨9075332854487839922718115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12100443805983786563624153 9075332854487839922718115)
                  ·
                    refine ⟨13612999281731759884077173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9075332854487839922718115 13612999281731759884077173)
                    ·
                      refine ⟨1276218682662352489132235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13612999281731759884077173 1276218682662352489132235)
                      ·
                        rfl

theorem cell23_2485427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_2485427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485427 prefixEnd_2485427 := by exact prefixLift 2485427
  have htrace : WordTrace (prefixWord ++ tailWord_2485427) baseStart_2485427 baseEnd_2485427 := by
    simpa [prefixWord, tailWord_2485427, baseEnd_2485427] using wordTrace_append hprefix tailTrace_2485427
  have hstable : (prefixWord ++ tailWord_2485427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485427).length < 2 ^ (prefixWord ++ tailWord_2485427).sum := by decide
  have hdescent : baseEnd_2485427 < baseStart_2485427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485462 : List Nat := [5, 2, 1, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_2485462 : Nat := 118140960795 + 2485462 * 2 ^ 59
def prefixEnd_2485462 : Nat := 4983230072969 + 3 ^ 40 * 2485462 * 2
def baseEnd_2485462 : Nat := 1276236654485259852194575

theorem tailTrace_2485462 : CollatzResearch.WordTrace tailWord_2485462 prefixEnd_2485462 1276236654485259852194575 := by
  unfold tailWord_2485462
  simp only [CollatzResearch.WordTrace]
  refine ⟨5665765407600195747492665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60434831014402087973255093 5665765407600195747492665)
  ·
    refine ⟨4249324055700146810619499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5665765407600195747492665 4249324055700146810619499)
    ·
      refine ⟨6373986083550220215929249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4249324055700146810619499 6373986083550220215929249)
      ·
        refine ⟨4780489562662665161946937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6373986083550220215929249 4780489562662665161946937)
        ·
          refine ⟨3585367171996998871460203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4780489562662665161946937 3585367171996998871460203)
          ·
            refine ⟨5378050757995498307190305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3585367171996998871460203 5378050757995498307190305)
            ·
              refine ⟨4033538068496623730392729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5378050757995498307190305 4033538068496623730392729)
              ·
                refine ⟨3025153551372467797794547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4033538068496623730392729 3025153551372467797794547)
                ·
                  refine ⟨4537730327058701696691821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3025153551372467797794547 4537730327058701696691821)
                  ·
                    refine ⟨1701648872647013136259433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4537730327058701696691821 1701648872647013136259433)
                    ·
                      refine ⟨1276236654485259852194575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1701648872647013136259433 1276236654485259852194575)
                      ·
                        rfl

theorem cell23_2485462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_2485462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485462 prefixEnd_2485462 := by exact prefixLift 2485462
  have htrace : WordTrace (prefixWord ++ tailWord_2485462) baseStart_2485462 baseEnd_2485462 := by
    simpa [prefixWord, tailWord_2485462, baseEnd_2485462] using wordTrace_append hprefix tailTrace_2485462
  have hstable : (prefixWord ++ tailWord_2485462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485462).length < 2 ^ (prefixWord ++ tailWord_2485462).sum := by decide
  have hdescent : baseEnd_2485462 < baseStart_2485462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485514 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_2485514 : Nat := 118140960795 + 2485514 * 2 ^ 59
def prefixEnd_2485514 : Nat := 4983230072969 + 3 ^ 40 * 2485514 * 2
def baseEnd_2485514 : Nat := 1276263355479293648744335

theorem tailTrace_2485514 : CollatzResearch.WordTrace tailWord_2485514 prefixEnd_2485514 1276263355479293648744335 := by
  unfold tailWord_2485514
  simp only [CollatzResearch.WordTrace]
  refine ⟨22663535779353686210193899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60436095411609829893850397 22663535779353686210193899)
  ·
    refine ⟨33995303669030529315290849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22663535779353686210193899 33995303669030529315290849)
    ·
      refine ⟨25496477751772896986468137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33995303669030529315290849 25496477751772896986468137)
      ·
        refine ⟨19122358313829672739851103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25496477751772896986468137 19122358313829672739851103)
        ·
          refine ⟨28683537470744509109776655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19122358313829672739851103 28683537470744509109776655)
          ·
            refine ⟨43025306206116763664664983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28683537470744509109776655 43025306206116763664664983)
            ·
              refine ⟨64537959309175145496997475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43025306206116763664664983 64537959309175145496997475)
              ·
                refine ⟨96806938963762718245496213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64537959309175145496997475 96806938963762718245496213)
                ·
                  refine ⟨4537825263926377417757635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96806938963762718245496213 4537825263926377417757635)
                  ·
                    refine ⟨6806737895889566126636453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4537825263926377417757635 6806737895889566126636453)
                    ·
                      refine ⟨1276263355479293648744335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6806737895889566126636453 1276263355479293648744335)
                      ·
                        rfl

theorem cell23_2485514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_2485514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485514 prefixEnd_2485514 := by exact prefixLift 2485514
  have htrace : WordTrace (prefixWord ++ tailWord_2485514) baseStart_2485514 baseEnd_2485514 := by
    simpa [prefixWord, tailWord_2485514, baseEnd_2485514] using wordTrace_append hprefix tailTrace_2485514
  have hstable : (prefixWord ++ tailWord_2485514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485514).length < 2 ^ (prefixWord ++ tailWord_2485514).sum := by decide
  have hdescent : baseEnd_2485514 < baseStart_2485514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485547 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 7]
def baseStart_2485547 : Nat := 118140960795 + 2485547 * 2 ^ 59
def prefixEnd_2485547 : Nat := 4983230072969 + 3 ^ 40 * 2485547 * 2
def baseEnd_2485547 : Nat := 1276280300340892019631683

theorem tailTrace_2485547 : CollatzResearch.WordTrace tailWord_2485547 prefixEnd_2485547 1276280300340892019631683 := by
  unfold tailWord_2485547
  simp only [CollatzResearch.WordTrace]
  refine ⟨90655346726295191476726895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60436897817530127651151263 90655346726295191476726895)
  ·
    refine ⟨135983020089442787215090343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90655346726295191476726895 135983020089442787215090343)
    ·
      refine ⟨203974530134164180822635515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135983020089442787215090343 203974530134164180822635515)
      ·
        refine ⟨305961795201246271233953273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203974530134164180822635515 305961795201246271233953273)
        ·
          refine ⟨229471346400934703425464955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305961795201246271233953273 229471346400934703425464955)
          ·
            refine ⟨344207019601402055138197433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229471346400934703425464955 344207019601402055138197433)
            ·
              refine ⟨258155264701051541353648075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344207019601402055138197433 258155264701051541353648075)
              ·
                refine ⟨387232897051577312030472113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258155264701051541353648075 387232897051577312030472113)
                ·
                  refine ⟨290424672788682984022854085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 387232897051577312030472113 290424672788682984022854085)
                  ·
                    refine ⟨54454626147878059504285141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 290424672788682984022854085 54454626147878059504285141)
                    ·
                      refine ⟨1276280300340892019631683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54454626147878059504285141 1276280300340892019631683)
                      ·
                        rfl

theorem cell23_2485547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 7].length) (baseStart_2485547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485547 prefixEnd_2485547 := by exact prefixLift 2485547
  have htrace : WordTrace (prefixWord ++ tailWord_2485547) baseStart_2485547 baseEnd_2485547 := by
    simpa [prefixWord, tailWord_2485547, baseEnd_2485547] using wordTrace_append hprefix tailTrace_2485547
  have hstable : (prefixWord ++ tailWord_2485547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485547).length < 2 ^ (prefixWord ++ tailWord_2485547).sum := by decide
  have hdescent : baseEnd_2485547 < baseStart_2485547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485565 : List Nat := [1, 4, 1, 5, 1, 1, 1, 1, 2, 4, 2]
def baseStart_2485565 : Nat := 118140960795 + 2485565 * 2 ^ 59
def prefixEnd_2485565 : Nat := 4983230072969 + 3 ^ 40 * 2485565 * 2
def baseEnd_2485565 : Nat := 1276289542992672949206601

theorem tailTrace_2485565 : CollatzResearch.WordTrace tailWord_2485565 prefixEnd_2485565 1276289542992672949206601 := by
  unfold tailWord_2485565
  simp only [CollatzResearch.WordTrace]
  refine ⟨90656003240229980550882149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60437335493486653700588099 90656003240229980550882149)
  ·
    refine ⟨16998000607543121353290403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90656003240229980550882149 16998000607543121353290403)
    ·
      refine ⟨25497000911314682029935605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16998000607543121353290403 25497000911314682029935605)
      ·
        refine ⟨2390343835435751440306463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25497000911314682029935605 2390343835435751440306463)
        ·
          refine ⟨3585515753153627160459695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2390343835435751440306463 3585515753153627160459695)
          ·
            refine ⟨5378273629730440740689543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3585515753153627160459695 5378273629730440740689543)
            ·
              refine ⟨8067410444595661111034315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5378273629730440740689543 8067410444595661111034315)
              ·
                refine ⟨12101115666893491666551473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8067410444595661111034315 12101115666893491666551473)
                ·
                  refine ⟨9075836750170118749913605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12101115666893491666551473 9075836750170118749913605)
                  ·
                    refine ⟨1701719390656897265608801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9075836750170118749913605 1701719390656897265608801)
                    ·
                      refine ⟨1276289542992672949206601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1701719390656897265608801 1276289542992672949206601)
                      ·
                        rfl

theorem cell23_2485565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_2485565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485565 prefixEnd_2485565 := by exact prefixLift 2485565
  have htrace : WordTrace (prefixWord ++ tailWord_2485565) baseStart_2485565 baseEnd_2485565 := by
    simpa [prefixWord, tailWord_2485565, baseEnd_2485565] using wordTrace_append hprefix tailTrace_2485565
  have hstable : (prefixWord ++ tailWord_2485565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485565).length < 2 ^ (prefixWord ++ tailWord_2485565).sum := by decide
  have hdescent : baseEnd_2485565 < baseStart_2485565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485584 : List Nat := [2, 1, 1, 1, 1, 5, 1, 3, 3, 5]
def baseStart_2485584 : Nat := 118140960795 + 2485584 * 2 ^ 59
def prefixEnd_2485584 : Nat := 4983230072969 + 3 ^ 40 * 2485584 * 2
def baseEnd_2485584 : Nat := 425433099708369458289671

theorem tailTrace_2485584 : CollatzResearch.WordTrace tailWord_2485584 prefixEnd_2485584 425433099708369458289671 := by
  unfold tailWord_2485584
  simp only [CollatzResearch.WordTrace]
  refine ⟨45328348113580573397911903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60437797484774097863882537 45328348113580573397911903)
  ·
    refine ⟨67992522170370860096867855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45328348113580573397911903 67992522170370860096867855)
    ·
      refine ⟨101988783255556290145301783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67992522170370860096867855 101988783255556290145301783)
      ·
        refine ⟨152983174883334435217952675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101988783255556290145301783 152983174883334435217952675)
        ·
          refine ⟨229474762325001652826929013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152983174883334435217952675 229474762325001652826929013)
          ·
            refine ⟨21513258967968904952524595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 229474762325001652826929013 21513258967968904952524595)
            ·
              refine ⟨32269888451953357428786893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21513258967968904952524595 32269888451953357428786893)
              ·
                refine ⟨12101208169482509035795085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32269888451953357428786893 12101208169482509035795085)
                ·
                  refine ⟨4537953063555940888423157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12101208169482509035795085 4537953063555940888423157)
                  ·
                    refine ⟨425433099708369458289671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4537953063555940888423157 425433099708369458289671)
                    ·
                      rfl

theorem cell23_2485584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 3, 3, 5].length) (baseStart_2485584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485584 prefixEnd_2485584 := by exact prefixLift 2485584
  have htrace : WordTrace (prefixWord ++ tailWord_2485584) baseStart_2485584 baseEnd_2485584 := by
    simpa [prefixWord, tailWord_2485584, baseEnd_2485584] using wordTrace_append hprefix tailTrace_2485584
  have hstable : (prefixWord ++ tailWord_2485584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485584).length < 2 ^ (prefixWord ++ tailWord_2485584).sum := by decide
  have hdescent : baseEnd_2485584 < baseStart_2485584 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485644 : List Nat := [2, 2, 1, 2, 1, 3, 3, 9]
def baseStart_2485644 : Nat := 118140960795 + 2485644 * 2 ^ 59
def prefixEnd_2485644 : Nat := 4983230072969 + 3 ^ 40 * 2485644 * 2
def baseEnd_2485644 : Nat := 47271485480162153337731

theorem tailTrace_2485644 : CollatzResearch.WordTrace tailWord_2485644 prefixEnd_2485644 47271485480162153337731 := by
  unfold tailWord_2485644
  simp only [CollatzResearch.WordTrace]
  refine ⟨45329442303471888521503993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60439256404629184695338657 45329442303471888521503993)
  ·
    refine ⟨33997081727603916391127995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45329442303471888521503993 33997081727603916391127995)
    ·
      refine ⟨50995622591405874586691993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33997081727603916391127995 50995622591405874586691993)
      ·
        refine ⟨38246716943554405940018995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50995622591405874586691993 38246716943554405940018995)
        ·
          refine ⟨57370075415331608910028493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38246716943554405940018995 57370075415331608910028493)
          ·
            refine ⟨21513778280749353341260685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57370075415331608910028493 21513778280749353341260685)
            ·
              refine ⟨8067666855281007502972757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21513778280749353341260685 8067666855281007502972757)
              ·
                refine ⟨47271485480162153337731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8067666855281007502972757 47271485480162153337731)
                ·
                  rfl

theorem cell23_2485644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 9].length) (baseStart_2485644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485644 prefixEnd_2485644 := by exact prefixLift 2485644
  have htrace : WordTrace (prefixWord ++ tailWord_2485644) baseStart_2485644 baseEnd_2485644 := by
    simpa [prefixWord, tailWord_2485644, baseEnd_2485644] using wordTrace_append hprefix tailTrace_2485644
  have hstable : (prefixWord ++ tailWord_2485644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485644).length < 2 ^ (prefixWord ++ tailWord_2485644).sum := by decide
  have hdescent : baseEnd_2485644 < baseStart_2485644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485658 : List Nat := [3, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3]
def baseStart_2485658 : Nat := 118140960795 + 2485658 * 2 ^ 59
def prefixEnd_2485658 : Nat := 4983230072969 + 3 ^ 40 * 2485658 * 2
def baseEnd_2485658 : Nat := 1276337296693541085343673

theorem tailTrace_2485658 : CollatzResearch.WordTrace tailWord_2485658 prefixEnd_2485658 1276337296693541085343673 := by
  unfold tailWord_2485658
  simp only [CollatzResearch.WordTrace]
  refine ⟨22664848807223264358504407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60439596819262038289345085 22664848807223264358504407)
  ·
    refine ⟨33997273210834896537756611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22664848807223264358504407 33997273210834896537756611)
    ·
      refine ⟨50995909816252344806634917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33997273210834896537756611 50995909816252344806634917)
      ·
        refine ⟨9561733090547314651244047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50995909816252344806634917 9561733090547314651244047)
        ·
          refine ⟨14342599635820971976866071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9561733090547314651244047 14342599635820971976866071)
          ·
            refine ⟨21513899453731457965299107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14342599635820971976866071 21513899453731457965299107)
            ·
              refine ⟨32270849180597186947948661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21513899453731457965299107 32270849180597186947948661)
              ·
                refine ⟨3025392110680986276370187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32270849180597186947948661 3025392110680986276370187)
                ·
                  refine ⟨4538088166021479414555281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3025392110680986276370187 4538088166021479414555281)
                  ·
                    refine ⟨3403566124516109560916461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4538088166021479414555281 3403566124516109560916461)
                    ·
                      refine ⟨1276337296693541085343673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3403566124516109560916461 1276337296693541085343673)
                      ·
                        rfl

theorem cell23_2485658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_2485658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485658 prefixEnd_2485658 := by exact prefixLift 2485658
  have htrace : WordTrace (prefixWord ++ tailWord_2485658) baseStart_2485658 baseEnd_2485658 := by
    simpa [prefixWord, tailWord_2485658, baseEnd_2485658] using wordTrace_append hprefix tailTrace_2485658
  have hstable : (prefixWord ++ tailWord_2485658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485658).length < 2 ^ (prefixWord ++ tailWord_2485658).sum := by decide
  have hdescent : baseEnd_2485658 < baseStart_2485658 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485661 : List Nat := [1, 4, 2, 1, 3, 3, 9]
def baseStart_2485661 : Nat := 118140960795 + 2485661 * 2 ^ 59
def prefixEnd_2485661 : Nat := 4983230072969 + 3 ^ 40 * 2485661 * 2
def baseEnd_2485661 : Nat := 15757269594265488563039

theorem tailTrace_2485661 : CollatzResearch.WordTrace tailWord_2485661 prefixEnd_2485661 15757269594265488563039 := by
  unfold tailWord_2485661
  simp only [CollatzResearch.WordTrace]
  refine ⟨90659504647882188946376837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60439669765254792630917891 90659504647882188946376837)
  ·
    refine ⟨16998657121477910427445657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90659504647882188946376837 16998657121477910427445657)
    ·
      refine ⟨12748992841108432820584243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16998657121477910427445657 12748992841108432820584243)
      ·
        refine ⟨19123489261662649230876365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12748992841108432820584243 19123489261662649230876365)
        ·
          refine ⟨7171308473123493461578637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19123489261662649230876365 7171308473123493461578637)
          ·
            refine ⟨2689240677421310048091989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7171308473123493461578637 2689240677421310048091989)
            ·
              refine ⟨15757269594265488563039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2689240677421310048091989 15757269594265488563039)
              ·
                rfl

theorem cell23_2485661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 9].length) (baseStart_2485661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485661 prefixEnd_2485661 := by exact prefixLift 2485661
  have htrace : WordTrace (prefixWord ++ tailWord_2485661) baseStart_2485661 baseEnd_2485661 := by
    simpa [prefixWord, tailWord_2485661, baseEnd_2485661] using wordTrace_append hprefix tailTrace_2485661
  have hstable : (prefixWord ++ tailWord_2485661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485661).length < 2 ^ (prefixWord ++ tailWord_2485661).sum := by decide
  have hdescent : baseEnd_2485661 < baseStart_2485661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485692 : List Nat := [2, 2, 2, 4, 2, 2, 1, 2, 1, 2, 3]
def baseStart_2485692 : Nat := 118140960795 + 2485692 * 2 ^ 59
def prefixEnd_2485692 : Nat := 4983230072969 + 3 ^ 40 * 2485692 * 2
def baseEnd_2485692 : Nat := 1276354755035793952318517

theorem tailTrace_2485692 : CollatzResearch.WordTrace tailWord_2485692 prefixEnd_2485692 1276354755035793952318517 := by
  unfold tailWord_2485692
  simp only [CollatzResearch.WordTrace]
  refine ⟨45330317655384940620377665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60440423540513254160503553 45330317655384940620377665)
  ·
    refine ⟨33997738241538705465283249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45330317655384940620377665 33997738241538705465283249)
    ·
      refine ⟨25498303681154029098962437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33997738241538705465283249 25498303681154029098962437)
      ·
        refine ⟨4780931940216380456055457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25498303681154029098962437 4780931940216380456055457)
        ·
          refine ⟨3585698955162285342041593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4780931940216380456055457 3585698955162285342041593)
          ·
            refine ⟨2689274216371714006531195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3585698955162285342041593 2689274216371714006531195)
            ·
              refine ⟨4033911324557571009796793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2689274216371714006531195 4033911324557571009796793)
              ·
                refine ⟨3025433493418178257347595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4033911324557571009796793 3025433493418178257347595)
                ·
                  refine ⟨4538150240127267386021393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3025433493418178257347595 4538150240127267386021393)
                  ·
                    refine ⟨3403612680095450539516045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4538150240127267386021393 3403612680095450539516045)
                    ·
                      refine ⟨1276354755035793952318517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3403612680095450539516045 1276354755035793952318517)
                      ·
                        rfl

theorem cell23_2485692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_2485692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485692 prefixEnd_2485692 := by exact prefixLift 2485692
  have htrace : WordTrace (prefixWord ++ tailWord_2485692) baseStart_2485692 baseEnd_2485692 := by
    simpa [prefixWord, tailWord_2485692, baseEnd_2485692] using wordTrace_append hprefix tailTrace_2485692
  have hstable : (prefixWord ++ tailWord_2485692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485692).length < 2 ^ (prefixWord ++ tailWord_2485692).sum := by decide
  have hdescent : baseEnd_2485692 < baseStart_2485692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485738 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 2, 6]
def baseStart_2485738 : Nat := 118140960795 + 2485738 * 2 ^ 59
def prefixEnd_2485738 : Nat := 4983230072969 + 3 ^ 40 * 2485738 * 2
def baseEnd_2485738 : Nat := 425459458381966924114435

theorem tailTrace_2485738 : CollatzResearch.WordTrace tailWord_2485738 prefixEnd_2485738 425459458381966924114435 := by
  unfold tailWord_2485738
  simp only [CollatzResearch.WordTrace]
  refine ⟨22665578267150807774232467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60441542045735487397953245 22665578267150807774232467)
  ·
    refine ⟨33998367400726211661348701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22665578267150807774232467 33998367400726211661348701)
    ·
      refine ⟨12749387775272329373005763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33998367400726211661348701 12749387775272329373005763)
      ·
        refine ⟨19124081662908494059508645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12749387775272329373005763 19124081662908494059508645)
        ·
          refine ⟨3585765311795342636157871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19124081662908494059508645 3585765311795342636157871)
          ·
            refine ⟨5378647967693013954236807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3585765311795342636157871 5378647967693013954236807)
            ·
              refine ⟨8067971951539520931355211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5378647967693013954236807 8067971951539520931355211)
              ·
                refine ⟨12101957927309281397032817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8067971951539520931355211 12101957927309281397032817)
                ·
                  refine ⟨9076468445481961047774613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12101957927309281397032817 9076468445481961047774613)
                  ·
                    refine ⟨425459458381966924114435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9076468445481961047774613 425459458381966924114435)
                    ·
                      rfl

theorem cell23_2485738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_2485738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485738 prefixEnd_2485738 := by exact prefixLift 2485738
  have htrace : WordTrace (prefixWord ++ tailWord_2485738) baseStart_2485738 baseEnd_2485738 := by
    simpa [prefixWord, tailWord_2485738, baseEnd_2485738] using wordTrace_append hprefix tailTrace_2485738
  have hstable : (prefixWord ++ tailWord_2485738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485738).length < 2 ^ (prefixWord ++ tailWord_2485738).sum := by decide
  have hdescent : baseEnd_2485738 < baseStart_2485738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485745 : List Nat := [1, 2, 2, 2, 3, 3, 2, 1, 1, 4, 2]
def baseStart_2485745 : Nat := 118140960795 + 2485745 * 2 ^ 59
def prefixEnd_2485745 : Nat := 4983230072969 + 3 ^ 40 * 2485745 * 2
def baseEnd_2485745 : Nat := 1276381969510482244955773

theorem tailTrace_2485745 : CollatzResearch.WordTrace tailWord_2485745 prefixEnd_2485745 1276381969510482244955773 := by
  unfold tailWord_2485745
  simp only [CollatzResearch.WordTrace]
  refine ⟨90662568379577871292434689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60441712253051914194956459 90662568379577871292434689)
  ·
    refine ⟨67996926284683403469326017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90662568379577871292434689 67996926284683403469326017)
    ·
      refine ⟨50997694713512552601994513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67996926284683403469326017 50997694713512552601994513)
      ·
        refine ⟨38248271035134414451495885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50997694713512552601994513 38248271035134414451495885)
        ·
          refine ⟨14343101638175405419310957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38248271035134414451495885 14343101638175405419310957)
          ·
            refine ⟨5378663114315777032241609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14343101638175405419310957 5378663114315777032241609)
            ·
              refine ⟨4033997335736832774181207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5378663114315777032241609 4033997335736832774181207)
              ·
                refine ⟨6050996003605249161271811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4033997335736832774181207 6050996003605249161271811)
                ·
                  refine ⟨9076494005407873741907717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6050996003605249161271811 9076494005407873741907717)
                  ·
                    refine ⟨1701842626013976326607697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9076494005407873741907717 1701842626013976326607697)
                    ·
                      refine ⟨1276381969510482244955773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1701842626013976326607697 1276381969510482244955773)
                      ·
                        rfl

theorem cell23_2485745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 4, 2].length) (baseStart_2485745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485745 prefixEnd_2485745 := by exact prefixLift 2485745
  have htrace : WordTrace (prefixWord ++ tailWord_2485745) baseStart_2485745 baseEnd_2485745 := by
    simpa [prefixWord, tailWord_2485745, baseEnd_2485745] using wordTrace_append hprefix tailTrace_2485745
  have hstable : (prefixWord ++ tailWord_2485745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485745).length < 2 ^ (prefixWord ++ tailWord_2485745).sum := by decide
  have hdescent : baseEnd_2485745 < baseStart_2485745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485762 : List Nat := [3, 4, 1, 2, 1, 1, 2, 2, 1, 4, 2]
def baseStart_2485762 : Nat := 118140960795 + 2485762 * 2 ^ 59
def prefixEnd_2485762 : Nat := 4983230072969 + 3 ^ 40 * 2485762 * 2
def baseEnd_2485762 : Nat := 1276390698681608678443195

theorem tailTrace_2485762 : CollatzResearch.WordTrace tailWord_2485762 prefixEnd_2485762 1276390698681608678443195 := by
  unfold tailWord_2485762
  simp only [CollatzResearch.WordTrace]
  refine ⟨22665797105129070798950885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60442125613677522130535693 22665797105129070798950885)
  ·
    refine ⟨4249836957211700774803291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22665797105129070798950885 4249836957211700774803291)
    ·
      refine ⟨6374755435817551162204937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4249836957211700774803291 6374755435817551162204937)
      ·
        refine ⟨4781066576863163371653703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6374755435817551162204937 4781066576863163371653703)
        ·
          refine ⟨7171599865294745057480555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4781066576863163371653703 7171599865294745057480555)
          ·
            refine ⟨10757399797942117586220833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7171599865294745057480555 10757399797942117586220833)
            ·
              refine ⟨8068049848456588189665625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10757399797942117586220833 8068049848456588189665625)
              ·
                refine ⟨6051037386342441142249219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8068049848456588189665625 6051037386342441142249219)
                ·
                  refine ⟨9076556079513661713373829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6051037386342441142249219 9076556079513661713373829)
                  ·
                    refine ⟨1701854264908811571257593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9076556079513661713373829 1701854264908811571257593)
                    ·
                      refine ⟨1276390698681608678443195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1701854264908811571257593 1276390698681608678443195)
                      ·
                        rfl

theorem cell23_2485762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_2485762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485762 prefixEnd_2485762 := by exact prefixLift 2485762
  have htrace : WordTrace (prefixWord ++ tailWord_2485762) baseStart_2485762 baseEnd_2485762 := by
    simpa [prefixWord, tailWord_2485762, baseEnd_2485762] using wordTrace_append hprefix tailTrace_2485762
  have hstable : (prefixWord ++ tailWord_2485762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485762).length < 2 ^ (prefixWord ++ tailWord_2485762).sum := by decide
  have hdescent : baseEnd_2485762 < baseStart_2485762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485768 : List Nat := [2, 1, 3, 2, 1, 1, 3, 5, 5]
def baseStart_2485768 : Nat := 118140960795 + 2485768 * 2 ^ 59
def prefixEnd_2485768 : Nat := 4983230072969 + 3 ^ 40 * 2485768 * 2
def baseEnd_2485768 : Nat := 141821531062837294996463

theorem tailTrace_2485768 : CollatzResearch.WordTrace tailWord_2485768 prefixEnd_2485768 141821531062837294996463 := by
  unfold tailWord_2485768
  simp only [CollatzResearch.WordTrace]
  refine ⟨45331703629247273110260979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60442271505663030813681305 45331703629247273110260979)
  ·
    refine ⟨67997555443870909665391469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45331703629247273110260979 67997555443870909665391469)
    ·
      refine ⟨25499083291451591124521801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67997555443870909665391469 25499083291451591124521801)
      ·
        refine ⟨19124312468588693343391351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25499083291451591124521801 19124312468588693343391351)
        ·
          refine ⟨28686468702883040015087027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19124312468588693343391351 28686468702883040015087027)
          ·
            refine ⟨43029703054324560022630541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28686468702883040015087027 43029703054324560022630541)
            ·
              refine ⟨16136138645371710008486453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43029703054324560022630541 16136138645371710008486453)
              ·
                refine ⟨1512762998003597813295605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16136138645371710008486453 1512762998003597813295605)
                ·
                  refine ⟨141821531062837294996463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1512762998003597813295605 141821531062837294996463)
                  ·
                    rfl

theorem cell23_2485768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 5, 5].length) (baseStart_2485768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485768 prefixEnd_2485768 := by exact prefixLift 2485768
  have htrace : WordTrace (prefixWord ++ tailWord_2485768) baseStart_2485768 baseEnd_2485768 := by
    simpa [prefixWord, tailWord_2485768, baseEnd_2485768] using wordTrace_append hprefix tailTrace_2485768
  have hstable : (prefixWord ++ tailWord_2485768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485768).length < 2 ^ (prefixWord ++ tailWord_2485768).sum := by decide
  have hdescent : baseEnd_2485768 < baseStart_2485768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485773 : List Nat := [1, 7, 1, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_2485773 : Nat := 118140960795 + 2485773 * 2 ^ 59
def prefixEnd_2485773 : Nat := 4983230072969 + 3 ^ 40 * 2485773 * 2
def baseEnd_2485773 : Nat := 1276396346968808135405645

theorem tailTrace_2485773 : CollatzResearch.WordTrace tailWord_2485773 prefixEnd_2485773 1276396346968808135405645 := by
  unfold tailWord_2485773
  simp only [CollatzResearch.WordTrace]
  refine ⟨90663589623476432074453973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60442393082317621382969315 90663589623476432074453973)
  ·
    refine ⟨2124927881800228876745015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 90663589623476432074453973 2124927881800228876745015)
    ·
      refine ⟨3187391822700343315117523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2124927881800228876745015 3187391822700343315117523)
      ·
        refine ⟨4781087734050514972676285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3187391822700343315117523 4781087734050514972676285)
        ·
          refine ⟨1792907900268943114753607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4781087734050514972676285 1792907900268943114753607)
          ·
            refine ⟨2689361850403414672130411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792907900268943114753607 2689361850403414672130411)
            ·
              refine ⟨4034042775605122008195617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2689361850403414672130411 4034042775605122008195617)
              ·
                refine ⟨3025532081703841506146713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4034042775605122008195617 3025532081703841506146713)
                ·
                  refine ⟨2269149061277881129610035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3025532081703841506146713 2269149061277881129610035)
                  ·
                    refine ⟨3403723591916821694415053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2269149061277881129610035 3403723591916821694415053)
                    ·
                      refine ⟨1276396346968808135405645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3403723591916821694415053 1276396346968808135405645)
                      ·
                        rfl

theorem cell23_2485773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_2485773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485773 prefixEnd_2485773 := by exact prefixLift 2485773
  have htrace : WordTrace (prefixWord ++ tailWord_2485773) baseStart_2485773 baseEnd_2485773 := by
    simpa [prefixWord, tailWord_2485773, baseEnd_2485773] using wordTrace_append hprefix tailTrace_2485773
  have hstable : (prefixWord ++ tailWord_2485773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485773).length < 2 ^ (prefixWord ++ tailWord_2485773).sum := by decide
  have hdescent : baseEnd_2485773 < baseStart_2485773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485791 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 5]
def baseStart_2485791 : Nat := 118140960795 + 2485791 * 2 ^ 59
def prefixEnd_2485791 : Nat := 4983230072969 + 3 ^ 40 * 2485791 * 2
def baseEnd_2485791 : Nat := 1276405589620589064980561

theorem tailTrace_2485791 : CollatzResearch.WordTrace tailWord_2485791 prefixEnd_2485791 1276405589620589064980561 := by
  unfold tailWord_2485791
  simp only [CollatzResearch.WordTrace]
  refine ⟨90664246137411221148609227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60442830758274147432406151 90664246137411221148609227)
  ·
    refine ⟨135996369206116831722913841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90664246137411221148609227 135996369206116831722913841)
    ·
      refine ⟨101997276904587623792185381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135996369206116831722913841 101997276904587623792185381)
      ·
        refine ⟨19124489419610179461034759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101997276904587623792185381 19124489419610179461034759)
        ·
          refine ⟨28686734129415269191552139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19124489419610179461034759 28686734129415269191552139)
          ·
            refine ⟨43030101194122903787328209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28686734129415269191552139 43030101194122903787328209)
            ·
              refine ⟨32272575895592177840496157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43030101194122903787328209 32272575895592177840496157)
              ·
                refine ⟨12102215960847066690186059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32272575895592177840496157 12102215960847066690186059)
                ·
                  refine ⟨18153323941270600035279089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12102215960847066690186059 18153323941270600035279089)
                  ·
                    refine ⟨13614992955952950026459317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18153323941270600035279089 13614992955952950026459317)
                    ·
                      refine ⟨1276405589620589064980561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13614992955952950026459317 1276405589620589064980561)
                      ·
                        rfl

theorem cell23_2485791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_2485791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485791 prefixEnd_2485791 := by exact prefixLift 2485791
  have htrace : WordTrace (prefixWord ++ tailWord_2485791) baseStart_2485791 baseEnd_2485791 := by
    simpa [prefixWord, tailWord_2485791, baseEnd_2485791] using wordTrace_append hprefix tailTrace_2485791
  have hstable : (prefixWord ++ tailWord_2485791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485791).length < 2 ^ (prefixWord ++ tailWord_2485791).sum := by decide
  have hdescent : baseEnd_2485791 < baseStart_2485791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485818 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4]
def baseStart_2485818 : Nat := 118140960795 + 2485818 * 2 ^ 59
def prefixEnd_2485818 : Nat := 4983230072969 + 3 ^ 40 * 2485818 * 2
def baseEnd_2485818 : Nat := 1276419453598260459342937

theorem tailTrace_2485818 : CollatzResearch.WordTrace tailWord_2485818 prefixEnd_2485818 1276419453598260459342937 := by
  unfold tailWord_2485818
  simp only [CollatzResearch.WordTrace]
  refine ⟨22666307727078351189960527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60443487272208936506561405 22666307727078351189960527)
  ·
    refine ⟨33999461590617526784940791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22666307727078351189960527 33999461590617526784940791)
    ·
      refine ⟨50999192385926290177411187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33999461590617526784940791 50999192385926290177411187)
      ·
        refine ⟨76498788578889435266116781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50999192385926290177411187 76498788578889435266116781)
        ·
          refine ⟨28687045717083538224793793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76498788578889435266116781 28687045717083538224793793)
          ·
            refine ⟨21515284287812653668595345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28687045717083538224793793 21515284287812653668595345)
            ·
              refine ⟨16136463215859490251446509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21515284287812653668595345 16136463215859490251446509)
              ·
                refine ⟨6051173705947308844292441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16136463215859490251446509 6051173705947308844292441)
                ·
                  refine ⟨4538380279460481633219331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6051173705947308844292441 4538380279460481633219331)
                  ·
                    refine ⟨6807570419190722449828997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4538380279460481633219331 6807570419190722449828997)
                    ·
                      refine ⟨1276419453598260459342937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6807570419190722449828997 1276419453598260459342937)
                      ·
                        rfl

theorem cell23_2485818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_2485818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485818 prefixEnd_2485818 := by exact prefixLift 2485818
  have htrace : WordTrace (prefixWord ++ tailWord_2485818) baseStart_2485818 baseEnd_2485818 := by
    simpa [prefixWord, tailWord_2485818, baseEnd_2485818] using wordTrace_append hprefix tailTrace_2485818
  have hstable : (prefixWord ++ tailWord_2485818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485818).length < 2 ^ (prefixWord ++ tailWord_2485818).sum := by decide
  have hdescent : baseEnd_2485818 < baseStart_2485818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485841 : List Nat := [1, 2, 2, 1, 3, 2, 1, 3, 8]
def baseStart_2485841 : Nat := 118140960795 + 2485841 * 2 ^ 59
def prefixEnd_2485841 : Nat := 4983230072969 + 3 ^ 40 * 2485841 * 2
def baseEnd_2485841 : Nat := 141825695961479318817259

theorem tailTrace_2485841 : CollatzResearch.WordTrace tailWord_2485841 prefixEnd_2485841 141825695961479318817259 := by
  unfold tailWord_2485841
  simp only [CollatzResearch.WordTrace]
  refine ⟨90666069787230079687929377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60444046524820053125286251 90666069787230079687929377)
  ·
    refine ⟨67999552340422559765947033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90666069787230079687929377 67999552340422559765947033)
    ·
      refine ⟨50999664255316919824460275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67999552340422559765947033 50999664255316919824460275)
      ·
        refine ⟨76499496382975379736690413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50999664255316919824460275 76499496382975379736690413)
        ·
          refine ⟨28687311143615767401258905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76499496382975379736690413 28687311143615767401258905)
          ·
            refine ⟨21515483357711825550944179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28687311143615767401258905 21515483357711825550944179)
            ·
              refine ⟨32273225036567738326416269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21515483357711825550944179 32273225036567738326416269)
              ·
                refine ⟨12102459388712901872406101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32273225036567738326416269 12102459388712901872406101)
                ·
                  refine ⟨141825695961479318817259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12102459388712901872406101 141825695961479318817259)
                  ·
                    rfl

theorem cell23_2485841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 8].length) (baseStart_2485841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485841 prefixEnd_2485841 := by exact prefixLift 2485841
  have htrace : WordTrace (prefixWord ++ tailWord_2485841) baseStart_2485841 baseEnd_2485841 := by
    simpa [prefixWord, tailWord_2485841, baseEnd_2485841] using wordTrace_append hprefix tailTrace_2485841
  have hstable : (prefixWord ++ tailWord_2485841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485841).length < 2 ^ (prefixWord ++ tailWord_2485841).sum := by decide
  have hdescent : baseEnd_2485841 < baseStart_2485841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485919 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 3, 1, 3]
def baseStart_2485919 : Nat := 118140960795 + 2485919 * 2 ^ 59
def prefixEnd_2485919 : Nat := 4983230072969 + 3 ^ 40 * 2485919 * 2
def baseEnd_2485919 : Nat := 1276471315144364564179973

theorem tailTrace_2485919 : CollatzResearch.WordTrace tailWord_2485919 prefixEnd_2485919 1276471315144364564179973 := by
  unfold tailWord_2485919
  simp only [CollatzResearch.WordTrace]
  refine ⟨90668914680947499009268811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60445943120631666006179207 90668914680947499009268811)
  ·
    refine ⟨136003372021421248513903217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90668914680947499009268811 136003372021421248513903217)
    ·
      refine ⟨102002529016065936385427413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136003372021421248513903217 102002529016065936385427413)
      ·
        refine ⟨2390684273814045384033455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 102002529016065936385427413 2390684273814045384033455)
        ·
          refine ⟨3586026410721068076050183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2390684273814045384033455 3586026410721068076050183)
          ·
            refine ⟨5379039616081602114075275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3586026410721068076050183 5379039616081602114075275)
            ·
              refine ⟨8068559424122403171112913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5379039616081602114075275 8068559424122403171112913)
              ·
                refine ⟨6051419568091802378334685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8068559424122403171112913 6051419568091802378334685)
                ·
                  refine ⟨2269282338034425891875507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6051419568091802378334685 2269282338034425891875507)
                  ·
                    refine ⟨3403923507051638837813261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2269282338034425891875507 3403923507051638837813261)
                    ·
                      refine ⟨1276471315144364564179973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3403923507051638837813261 1276471315144364564179973)
                      ·
                        rfl

theorem cell23_2485919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_2485919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485919 prefixEnd_2485919 := by exact prefixLift 2485919
  have htrace : WordTrace (prefixWord ++ tailWord_2485919) baseStart_2485919 baseEnd_2485919 := by
    simpa [prefixWord, tailWord_2485919, baseEnd_2485919] using wordTrace_append hprefix tailTrace_2485919
  have hstable : (prefixWord ++ tailWord_2485919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485919).length < 2 ^ (prefixWord ++ tailWord_2485919).sum := by decide
  have hdescent : baseEnd_2485919 < baseStart_2485919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485948 : List Nat := [2, 2, 2, 3, 1, 3, 10]
def baseStart_2485948 : Nat := 118140960795 + 2485948 * 2 ^ 59
def prefixEnd_2485948 : Nat := 4983230072969 + 3 ^ 40 * 2485948 * 2
def baseEnd_2485948 : Nat := 15759088963991912971819

theorem tailTrace_2485948 : CollatzResearch.WordTrace tailWord_2485948 prefixEnd_2485948 15759088963991912971819 := by
  unfold tailWord_2485948
  simp only [CollatzResearch.WordTrace]
  refine ⟨45334986198921218481037249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60446648265228291308049665 45334986198921218481037249)
  ·
    refine ⟨34001239649190913860777937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45334986198921218481037249 34001239649190913860777937)
    ·
      refine ⟨25500929736893185395583453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34001239649190913860777937 25500929736893185395583453)
      ·
        refine ⟨9562848651334944523343795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25500929736893185395583453 9562848651334944523343795)
        ·
          refine ⟨14344272977002416785015693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9562848651334944523343795 14344272977002416785015693)
          ·
            refine ⟨5379102366375906294380885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14344272977002416785015693 5379102366375906294380885)
            ·
              refine ⟨15759088963991912971819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5379102366375906294380885 15759088963991912971819)
              ·
                rfl

theorem cell23_2485948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 10].length) (baseStart_2485948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485948 prefixEnd_2485948 := by exact prefixLift 2485948
  have htrace : WordTrace (prefixWord ++ tailWord_2485948) baseStart_2485948 baseEnd_2485948 := by
    simpa [prefixWord, tailWord_2485948, baseEnd_2485948] using wordTrace_append hprefix tailTrace_2485948
  have hstable : (prefixWord ++ tailWord_2485948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485948).length < 2 ^ (prefixWord ++ tailWord_2485948).sum := by decide
  have hdescent : baseEnd_2485948 < baseStart_2485948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485959 : List Nat := [1, 1, 4, 1, 1, 1, 3, 6, 1, 2, 2]
def baseStart_2485959 : Nat := 118140960795 + 2485959 * 2 ^ 59
def prefixEnd_2485959 : Nat := 4983230072969 + 3 ^ 40 * 2485959 * 2
def baseEnd_2485959 : Nat := 1276491854370544407679789

theorem tailTrace_2485959 : CollatzResearch.WordTrace tailWord_2485959 prefixEnd_2485959 1276491854370544407679789 := by
  unfold tailWord_2485959
  simp only [CollatzResearch.WordTrace]
  refine ⟨90670373600802585840724931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60446915733868390560483287 90670373600802585840724931)
  ·
    refine ⟨136005560401203878761087397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90670373600802585840724931 136005560401203878761087397)
    ·
      refine ⟨25501042575225727267703887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136005560401203878761087397 25501042575225727267703887)
      ·
        refine ⟨38251563862838590901555831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25501042575225727267703887 38251563862838590901555831)
        ·
          refine ⟨57377345794257886352333747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38251563862838590901555831 57377345794257886352333747)
          ·
            refine ⟨86066018691386829528500621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57377345794257886352333747 86066018691386829528500621)
            ·
              refine ⟨32274757009270061073187733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86066018691386829528500621 32274757009270061073187733)
              ·
                refine ⟨1512879234809534112805675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32274757009270061073187733 1512879234809534112805675)
                ·
                  refine ⟨2269318852214301169208513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1512879234809534112805675 2269318852214301169208513)
                  ·
                    refine ⟨1701989139160725876906385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2269318852214301169208513 1701989139160725876906385)
                    ·
                      refine ⟨1276491854370544407679789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1701989139160725876906385 1276491854370544407679789)
                      ·
                        rfl

theorem cell23_2485959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 6, 1, 2, 2].length) (baseStart_2485959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485959 prefixEnd_2485959 := by exact prefixLift 2485959
  have htrace : WordTrace (prefixWord ++ tailWord_2485959) baseStart_2485959 baseEnd_2485959 := by
    simpa [prefixWord, tailWord_2485959, baseEnd_2485959] using wordTrace_append hprefix tailTrace_2485959
  have hstable : (prefixWord ++ tailWord_2485959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485959).length < 2 ^ (prefixWord ++ tailWord_2485959).sum := by decide
  have hdescent : baseEnd_2485959 < baseStart_2485959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485972 : List Nat := [2, 4, 1, 3, 1, 1, 3, 1, 1, 2, 4]
def baseStart_2485972 : Nat := 118140960795 + 2485972 * 2 ^ 59
def prefixEnd_2485972 : Nat := 4983230072969 + 3 ^ 40 * 2485972 * 2
def baseEnd_2485972 : Nat := 1276498529619052856817229

theorem tailTrace_2485972 : CollatzResearch.WordTrace tailWord_2485972 prefixEnd_2485972 1276498529619052856817229 := by
  unfold tailWord_2485972
  simp only [CollatzResearch.WordTrace]
  refine ⟨45335423874877744530474085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60447231833170326040632113 45335423874877744530474085)
  ·
    refine ⟨8500391976539577099463891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45335423874877744530474085 8500391976539577099463891)
    ·
      refine ⟨12750587964809365649195837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8500391976539577099463891 12750587964809365649195837)
      ·
        refine ⟨4781470486803512118448439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12750587964809365649195837 4781470486803512118448439)
        ·
          refine ⟨7172205730205268177672659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4781470486803512118448439 7172205730205268177672659)
          ·
            refine ⟨10758308595307902266508989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7172205730205268177672659 10758308595307902266508989)
            ·
              refine ⟨4034365723240463349940871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10758308595307902266508989 4034365723240463349940871)
              ·
                refine ⟨6051548584860695024911307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4034365723240463349940871 6051548584860695024911307)
                ·
                  refine ⟨9077322877291042537366961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6051548584860695024911307 9077322877291042537366961)
                  ·
                    refine ⟨6807992157968281903025221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9077322877291042537366961 6807992157968281903025221)
                    ·
                      refine ⟨1276498529619052856817229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6807992157968281903025221 1276498529619052856817229)
                      ·
                        rfl

theorem cell23_2485972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_2485972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485972 prefixEnd_2485972 := by exact prefixLift 2485972
  have htrace : WordTrace (prefixWord ++ tailWord_2485972) baseStart_2485972 baseEnd_2485972 := by
    simpa [prefixWord, tailWord_2485972, baseEnd_2485972] using wordTrace_append hprefix tailTrace_2485972
  have hstable : (prefixWord ++ tailWord_2485972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485972).length < 2 ^ (prefixWord ++ tailWord_2485972).sum := by decide
  have hdescent : baseEnd_2485972 < baseStart_2485972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485988 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_2485988 : Nat := 118140960795 + 2485988 * 2 ^ 59
def prefixEnd_2485988 : Nat := 4983230072969 + 3 ^ 40 * 2485988 * 2
def baseEnd_2485988 : Nat := 1276506745309524794217155

theorem tailTrace_2485988 : CollatzResearch.WordTrace tailWord_2485988 prefixEnd_2485988 1276506745309524794217155 := by
  unfold tailWord_2485988
  simp only [CollatzResearch.WordTrace]
  refine ⟨45335715658848761896765309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60447620878465015862353745 45335715658848761896765309)
  ·
    refine ⟨17000893372068285711286991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45335715658848761896765309 17000893372068285711286991)
    ·
      refine ⟨25501340058102428566930487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17000893372068285711286991 25501340058102428566930487)
      ·
        refine ⟨38252010087153642850395731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25501340058102428566930487 38252010087153642850395731)
        ·
          refine ⟨57378015130730464275593597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38252010087153642850395731 57378015130730464275593597)
          ·
            refine ⟨21516755674023924103347599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57378015130730464275593597 21516755674023924103347599)
            ·
              refine ⟨32275133511035886155021399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21516755674023924103347599 32275133511035886155021399)
              ·
                refine ⟨48412700266553829232532099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32275133511035886155021399 48412700266553829232532099)
                ·
                  refine ⟨72619050399830743848798149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48412700266553829232532099 72619050399830743848798149)
                  ·
                    refine ⟨13616071949968264471649653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72619050399830743848798149 13616071949968264471649653)
                    ·
                      refine ⟨1276506745309524794217155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13616071949968264471649653 1276506745309524794217155)
                      ·
                        rfl

theorem cell23_2485988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_2485988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485988 prefixEnd_2485988 := by exact prefixLift 2485988
  have htrace : WordTrace (prefixWord ++ tailWord_2485988) baseStart_2485988 baseEnd_2485988 := by
    simpa [prefixWord, tailWord_2485988, baseEnd_2485988] using wordTrace_append hprefix tailTrace_2485988
  have hstable : (prefixWord ++ tailWord_2485988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485988).length < 2 ^ (prefixWord ++ tailWord_2485988).sum := by decide
  have hdescent : baseEnd_2485988 < baseStart_2485988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2485992 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_2485992 : Nat := 118140960795 + 2485992 * 2 ^ 59
def prefixEnd_2485992 : Nat := 4983230072969 + 3 ^ 40 * 2485992 * 2
def baseEnd_2485992 : Nat := 1276508799232142778567137

theorem tailTrace_2485992 : CollatzResearch.WordTrace tailWord_2485992 prefixEnd_2485992 1276508799232142778567137 := by
  unfold tailWord_2485992
  simp only [CollatzResearch.WordTrace]
  refine ⟨45335788604841516238338115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60447718139788688317784153 45335788604841516238338115)
  ·
    refine ⟨68003682907262274357507173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45335788604841516238338115 68003682907262274357507173)
    ·
      refine ⟨12750690545111676442032595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68003682907262274357507173 12750690545111676442032595)
      ·
        refine ⟨19126035817667514663048893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12750690545111676442032595 19126035817667514663048893)
        ·
          refine ⟨7172263431625317998643335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19126035817667514663048893 7172263431625317998643335)
          ·
            refine ⟨10758395147437976997965003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7172263431625317998643335 10758395147437976997965003)
            ·
              refine ⟨16137592721156965496947505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10758395147437976997965003 16137592721156965496947505)
              ·
                refine ⟨12103194540867724122710629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16137592721156965496947505 12103194540867724122710629)
                ·
                  refine ⟨2269348976412698273008243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12103194540867724122710629 2269348976412698273008243)
                  ·
                    refine ⟨3404023464619047409512365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2269348976412698273008243 3404023464619047409512365)
                    ·
                      refine ⟨1276508799232142778567137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3404023464619047409512365 1276508799232142778567137)
                      ·
                        rfl

theorem cell23_2485992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_2485992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2485992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2485992 prefixEnd_2485992 := by exact prefixLift 2485992
  have htrace : WordTrace (prefixWord ++ tailWord_2485992) baseStart_2485992 baseEnd_2485992 := by
    simpa [prefixWord, tailWord_2485992, baseEnd_2485992] using wordTrace_append hprefix tailTrace_2485992
  have hstable : (prefixWord ++ tailWord_2485992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2485992).length < 2 ^ (prefixWord ++ tailWord_2485992).sum := by decide
  have hdescent : baseEnd_2485992 < baseStart_2485992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2485992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486008 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 2, 6]
def baseStart_2486008 : Nat := 118140960795 + 2486008 * 2 ^ 59
def prefixEnd_2486008 : Nat := 4983230072969 + 3 ^ 40 * 2486008 * 2
def baseEnd_2486008 : Nat := 425505671640871571989021

theorem tailTrace_2486008 : CollatzResearch.WordTrace tailWord_2486008 prefixEnd_2486008 425505671640871571989021 := by
  unfold tailWord_2486008
  simp only [CollatzResearch.WordTrace]
  refine ⟨45336080388812533604629339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60448107185083378139505785 45336080388812533604629339)
  ·
    refine ⟨68004120583218800406944009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45336080388812533604629339 68004120583218800406944009)
    ·
      refine ⟨51003090437414100305208007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68004120583218800406944009 51003090437414100305208007)
      ·
        refine ⟨76504635656121150457812011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51003090437414100305208007 76504635656121150457812011)
        ·
          refine ⟨114756953484181725686718017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76504635656121150457812011 114756953484181725686718017)
          ·
            refine ⟨86067715113136294265038513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114756953484181725686718017 86067715113136294265038513)
            ·
              refine ⟨64550786334852220698778885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86067715113136294265038513 64550786334852220698778885)
              ·
                refine ⟨12103272437784791381021041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64550786334852220698778885 12103272437784791381021041)
                ·
                  refine ⟨9077454328338593535765781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12103272437784791381021041 9077454328338593535765781)
                  ·
                    refine ⟨425505671640871571989021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9077454328338593535765781 425505671640871571989021)
                    ·
                      rfl

theorem cell23_2486008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_2486008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486008 prefixEnd_2486008 := by exact prefixLift 2486008
  have htrace : WordTrace (prefixWord ++ tailWord_2486008) baseStart_2486008 baseEnd_2486008 := by
    simpa [prefixWord, tailWord_2486008, baseEnd_2486008] using wordTrace_append hprefix tailTrace_2486008
  have hstable : (prefixWord ++ tailWord_2486008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486008).length < 2 ^ (prefixWord ++ tailWord_2486008).sum := by decide
  have hdescent : baseEnd_2486008 < baseStart_2486008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486026 : List Nat := [3, 1, 2, 2, 1, 5, 2, 1, 2, 1, 3]
def baseStart_2486026 : Nat := 118140960795 + 2486026 * 2 ^ 59
def prefixEnd_2486026 : Nat := 4983230072969 + 3 ^ 40 * 2486026 * 2
def baseEnd_2486026 : Nat := 1276526257574395645541981

theorem tailTrace_2486026 : CollatzResearch.WordTrace tailWord_2486026 prefixEnd_2486026 1276526257574395645541981 := by
  unfold tailWord_2486026
  simp only [CollatzResearch.WordTrace]
  refine ⟨22668204322889964070853483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60448544861039904188942621 22668204322889964070853483)
  ·
    refine ⟨34002306484334946106280225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22668204322889964070853483 34002306484334946106280225)
    ·
      refine ⟨25501729863251209579710169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34002306484334946106280225 25501729863251209579710169)
      ·
        refine ⟨19126297397438407184782627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25501729863251209579710169 19126297397438407184782627)
        ·
          refine ⟨28689446096157610777173941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19126297397438407184782627 28689446096157610777173941)
          ·
            refine ⟨2689635571514776010360057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28689446096157610777173941 2689635571514776010360057)
            ·
              refine ⟨2017226678636082007770043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2689635571514776010360057 2017226678636082007770043)
              ·
                refine ⟨3025840017954123011655065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2017226678636082007770043 3025840017954123011655065)
                ·
                  refine ⟨2269380013465592258741299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3025840017954123011655065 2269380013465592258741299)
                  ·
                    refine ⟨3404070020198388388111949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2269380013465592258741299 3404070020198388388111949)
                    ·
                      refine ⟨1276526257574395645541981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3404070020198388388111949 1276526257574395645541981)
                      ·
                        rfl

theorem cell23_2486026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_2486026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486026 prefixEnd_2486026 := by exact prefixLift 2486026
  have htrace : WordTrace (prefixWord ++ tailWord_2486026) baseStart_2486026 baseEnd_2486026 := by
    simpa [prefixWord, tailWord_2486026, baseEnd_2486026] using wordTrace_append hprefix tailTrace_2486026
  have hstable : (prefixWord ++ tailWord_2486026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486026).length < 2 ^ (prefixWord ++ tailWord_2486026).sum := by decide
  have hdescent : baseEnd_2486026 < baseStart_2486026 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486066 : List Nat := [3, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2]
def baseStart_2486066 : Nat := 118140960795 + 2486066 * 2 ^ 59
def prefixEnd_2486066 : Nat := 4983230072969 + 3 ^ 40 * 2486066 * 2
def baseEnd_2486066 : Nat := 1276546796800575489041797

theorem tailTrace_2486066 : CollatzResearch.WordTrace tailWord_2486066 prefixEnd_2486066 1276546796800575489041797 := by
  unfold tailWord_2486066
  simp only [CollatzResearch.WordTrace]
  refine ⟨22668569052853735778717513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60449517474276628743246701 22668569052853735778717513)
  ·
    refine ⟨17001426789640301834038135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22668569052853735778717513 17001426789640301834038135)
    ·
      refine ⟨25502140184460452751057203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17001426789640301834038135 25502140184460452751057203)
      ·
        refine ⟨38253210276690679126585805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25502140184460452751057203 38253210276690679126585805)
        ·
          refine ⟨14344953853759004672469677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38253210276690679126585805 14344953853759004672469677)
          ·
            refine ⟨5379357695159626752176129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14344953853759004672469677 5379357695159626752176129)
            ·
              refine ⟨4034518271369720064132097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5379357695159626752176129 4034518271369720064132097)
              ·
                refine ⟨3025888703527290048099073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4034518271369720064132097 3025888703527290048099073)
                ·
                  refine ⟨2269416527645467536074305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3025888703527290048099073 2269416527645467536074305)
                  ·
                    refine ⟨1702062395734100652055729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2269416527645467536074305 1702062395734100652055729)
                    ·
                      refine ⟨1276546796800575489041797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1702062395734100652055729 1276546796800575489041797)
                      ·
                        rfl

theorem cell23_2486066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2].length) (baseStart_2486066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486066 prefixEnd_2486066 := by exact prefixLift 2486066
  have htrace : WordTrace (prefixWord ++ tailWord_2486066) baseStart_2486066 baseEnd_2486066 := by
    simpa [prefixWord, tailWord_2486066, baseEnd_2486066] using wordTrace_append hprefix tailTrace_2486066
  have hstable : (prefixWord ++ tailWord_2486066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486066).length < 2 ^ (prefixWord ++ tailWord_2486066).sum := by decide
  have hdescent : baseEnd_2486066 < baseStart_2486066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486072 : List Nat := [2, 1, 2, 1, 3, 4, 1, 4, 5]
def baseStart_2486072 : Nat := 118140960795 + 2486072 * 2 ^ 59
def prefixEnd_2486072 : Nat := 4983230072969 + 3 ^ 40 * 2486072 * 2
def baseEnd_2486072 : Nat := 141838875298278051729641

theorem tailTrace_2486072 : CollatzResearch.WordTrace tailWord_2486072 prefixEnd_2486072 141838875298278051729641 := by
  unfold tailWord_2486072
  simp only [CollatzResearch.WordTrace]
  refine ⟨45337247524696603069794235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60449663366262137426392313 45337247524696603069794235)
  ·
    refine ⟨68005871287044904604691353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45337247524696603069794235 68005871287044904604691353)
    ·
      refine ⟨51004403465283678453518515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68005871287044904604691353 51004403465283678453518515)
      ·
        refine ⟨76506605197925517680277773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51004403465283678453518515 76506605197925517680277773)
        ·
          refine ⟨28689976949222069130104165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76506605197925517680277773 28689976949222069130104165)
          ·
            refine ⟨5379370677979137961894531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28689976949222069130104165 5379370677979137961894531)
            ·
              refine ⟨8069056016968706942841797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5379370677979137961894531 8069056016968706942841797)
              ·
                refine ⟨1512948003181632551782837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8069056016968706942841797 1512948003181632551782837)
                ·
                  refine ⟨141838875298278051729641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1512948003181632551782837 141838875298278051729641)
                  ·
                    rfl

theorem cell23_2486072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 5].length) (baseStart_2486072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486072 prefixEnd_2486072 := by exact prefixLift 2486072
  have htrace : WordTrace (prefixWord ++ tailWord_2486072) baseStart_2486072 baseEnd_2486072 := by
    simpa [prefixWord, tailWord_2486072, baseEnd_2486072] using wordTrace_append hprefix tailTrace_2486072
  have hstable : (prefixWord ++ tailWord_2486072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486072).length < 2 ^ (prefixWord ++ tailWord_2486072).sum := by decide
  have hdescent : baseEnd_2486072 < baseStart_2486072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486105 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 1, 3, 4]
def baseStart_2486105 : Nat := 118140960795 + 2486105 * 2 ^ 59
def prefixEnd_2486105 : Nat := 4983230072969 + 3 ^ 40 * 2486105 * 2
def baseEnd_2486105 : Nat := 1276566822546100836454117

theorem tailTrace_2486105 : CollatzResearch.WordTrace tailWord_2486105 prefixEnd_2486105 1276566822546100836454117 := by
  unfold tailWord_2486105
  simp only [CollatzResearch.WordTrace]
  refine ⟨90675698658273652775539769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60450465772182435183693179 90675698658273652775539769)
  ·
    refine ⟨68006773993705239581654827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90675698658273652775539769 68006773993705239581654827)
    ·
      refine ⟨102010160990557859372482241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68006773993705239581654827 102010160990557859372482241)
      ·
        refine ⟨76507620742918394529361681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102010160990557859372482241 76507620742918394529361681)
        ·
          refine ⟨57380715557188795897021261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76507620742918394529361681 57380715557188795897021261)
          ·
            refine ⟨21517768333945798461382973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57380715557188795897021261 21517768333945798461382973)
            ·
              refine ⟨8069163125229674423018615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21517768333945798461382973 8069163125229674423018615)
              ·
                refine ⟨12103744687844511634527923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8069163125229674423018615 12103744687844511634527923)
                ·
                  refine ⟨18155617031766767451791885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12103744687844511634527923 18155617031766767451791885)
                  ·
                    refine ⟨6808356386912537794421957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18155617031766767451791885 6808356386912537794421957)
                    ·
                      refine ⟨1276566822546100836454117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6808356386912537794421957 1276566822546100836454117)
                      ·
                        rfl

theorem cell23_2486105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_2486105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486105 prefixEnd_2486105 := by exact prefixLift 2486105
  have htrace : WordTrace (prefixWord ++ tailWord_2486105) baseStart_2486105 baseEnd_2486105 := by
    simpa [prefixWord, tailWord_2486105, baseEnd_2486105] using wordTrace_append hprefix tailTrace_2486105
  have hstable : (prefixWord ++ tailWord_2486105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486105).length < 2 ^ (prefixWord ++ tailWord_2486105).sum := by decide
  have hdescent : baseEnd_2486105 < baseStart_2486105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486125 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2486125 : Nat := 118140960795 + 2486125 * 2 ^ 59
def prefixEnd_2486125 : Nat := 4983230072969 + 3 ^ 40 * 2486125 * 2
def baseEnd_2486125 : Nat := 1276577092159190758204025

theorem tailTrace_2486125 : CollatzResearch.WordTrace tailWord_2486125 prefixEnd_2486125 1276577092159190758204025 := by
  unfold tailWord_2486125
  simp only [CollatzResearch.WordTrace]
  refine ⟨90676428118201196191267829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60450952078800797460845219 90676428118201196191267829)
  ·
    refine ⟨8500915136081362142931359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90676428118201196191267829 8500915136081362142931359)
    ·
      refine ⟨12751372704122043214397039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8500915136081362142931359 12751372704122043214397039)
      ·
        refine ⟨19127059056183064821595559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12751372704122043214397039 19127059056183064821595559)
        ·
          refine ⟨28690588584274597232393339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19127059056183064821595559 28690588584274597232393339)
          ·
            refine ⟨43035882876411895848590009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28690588584274597232393339 43035882876411895848590009)
            ·
              refine ⟨32276912157308921886442507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43035882876411895848590009 32276912157308921886442507)
              ·
                refine ⟨48415368235963382829663761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32276912157308921886442507 48415368235963382829663761)
                ·
                  refine ⟨36311526176972537122247821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48415368235963382829663761 36311526176972537122247821)
                  ·
                    refine ⟨13616822316364701420842933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36311526176972537122247821 13616822316364701420842933)
                    ·
                      refine ⟨1276577092159190758204025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13616822316364701420842933 1276577092159190758204025)
                      ·
                        rfl

theorem cell23_2486125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2486125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486125 prefixEnd_2486125 := by exact prefixLift 2486125
  have htrace : WordTrace (prefixWord ++ tailWord_2486125) baseStart_2486125 baseEnd_2486125 := by
    simpa [prefixWord, tailWord_2486125, baseEnd_2486125] using wordTrace_append hprefix tailTrace_2486125
  have hstable : (prefixWord ++ tailWord_2486125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486125).length < 2 ^ (prefixWord ++ tailWord_2486125).sum := by decide
  have hdescent : baseEnd_2486125 < baseStart_2486125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486155 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 3]
def baseStart_2486155 : Nat := 118140960795 + 2486155 * 2 ^ 59
def prefixEnd_2486155 : Nat := 4983230072969 + 3 ^ 40 * 2486155 * 2
def baseEnd_2486155 : Nat := 1276592496578825640828887

theorem tailTrace_2486155 : CollatzResearch.WordTrace tailWord_2486155 prefixEnd_2486155 1276592496578825640828887 := by
  unfold tailWord_2486155
  simp only [CollatzResearch.WordTrace]
  refine ⟨90677522308092511314859919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60451681538728340876573279 90677522308092511314859919)
  ·
    refine ⟨136016283462138766972289879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90677522308092511314859919 136016283462138766972289879)
    ·
      refine ⟨204024425193208150458434819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136016283462138766972289879 204024425193208150458434819)
      ·
        refine ⟨306036637789812225687652229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204024425193208150458434819 306036637789812225687652229)
        ·
          refine ⟨57381869585589792316434793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 306036637789812225687652229 57381869585589792316434793)
          ·
            refine ⟨43036402189192344237326095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57381869585589792316434793 43036402189192344237326095)
            ·
              refine ⟨64554603283788516355989143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43036402189192344237326095 64554603283788516355989143)
              ·
                refine ⟨96831904925682774533983715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64554603283788516355989143 96831904925682774533983715)
                ·
                  refine ⟨145247857388524161800975573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96831904925682774533983715 145247857388524161800975573)
                  ·
                    refine ⟨3404246657543535042210365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 145247857388524161800975573 3404246657543535042210365)
                    ·
                      refine ⟨1276592496578825640828887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3404246657543535042210365 1276592496578825640828887)
                      ·
                        rfl

theorem cell23_2486155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 7, 3].length) (baseStart_2486155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486155 prefixEnd_2486155 := by exact prefixLift 2486155
  have htrace : WordTrace (prefixWord ++ tailWord_2486155) baseStart_2486155 baseEnd_2486155 := by
    simpa [prefixWord, tailWord_2486155, baseEnd_2486155] using wordTrace_append hprefix tailTrace_2486155
  have hstable : (prefixWord ++ tailWord_2486155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486155).length < 2 ^ (prefixWord ++ tailWord_2486155).sum := by decide
  have hdescent : baseEnd_2486155 < baseStart_2486155 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486162 : List Nat := [3, 2, 3, 2, 1, 1, 1, 2, 8]
def baseStart_2486162 : Nat := 118140960795 + 2486162 * 2 ^ 59
def prefixEnd_2486162 : Nat := 4983230072969 + 3 ^ 40 * 2486162 * 2
def baseEnd_2486162 : Nat := 141844010104823012604595

theorem tailTrace_2486162 : CollatzResearch.WordTrace tailWord_2486162 prefixEnd_2486162 141844010104823012604595 := by
  unfold tailWord_2486162
  simp only [CollatzResearch.WordTrace]
  refine ⟨22669444404766787877591185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60451851746044767673576493 22669444404766787877591185)
  ·
    refine ⟨17002083303575090908193389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22669444404766787877591185 17002083303575090908193389)
    ·
      refine ⟨6375781238840659090572521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17002083303575090908193389 6375781238840659090572521)
      ·
        refine ⟨4781835929130494317929391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6375781238840659090572521 4781835929130494317929391)
        ·
          refine ⟨7172753893695741476894087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4781835929130494317929391 7172753893695741476894087)
          ·
            refine ⟨10759130840543612215341131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7172753893695741476894087 10759130840543612215341131)
            ·
              refine ⟨16138696260815418323011697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10759130840543612215341131 16138696260815418323011697)
              ·
                refine ⟨12104022195611563742258773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16138696260815418323011697 12104022195611563742258773)
                ·
                  refine ⟨141844010104823012604595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12104022195611563742258773 141844010104823012604595)
                  ·
                    rfl

theorem cell23_2486162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_2486162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486162 prefixEnd_2486162 := by exact prefixLift 2486162
  have htrace : WordTrace (prefixWord ++ tailWord_2486162) baseStart_2486162 baseEnd_2486162 := by
    simpa [prefixWord, tailWord_2486162, baseEnd_2486162] using wordTrace_append hprefix tailTrace_2486162
  have hstable : (prefixWord ++ tailWord_2486162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486162).length < 2 ^ (prefixWord ++ tailWord_2486162).sum := by decide
  have hdescent : baseEnd_2486162 < baseStart_2486162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486183 : List Nat := [1, 1, 6, 1, 2, 2, 3, 2, 1, 4]
def baseStart_2486183 : Nat := 118140960795 + 2486183 * 2 ^ 59
def prefixEnd_2486183 : Nat := 4983230072969 + 3 ^ 40 * 2486183 * 2
def baseEnd_2486183 : Nat := 425535624679050510426253

theorem tailTrace_2486183 : CollatzResearch.WordTrace tailWord_2486183 prefixEnd_2486183 425535624679050510426253 := by
  unfold tailWord_2486183
  simp only [CollatzResearch.WordTrace]
  refine ⟨90678543551991072096879203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60452362367994048064586135 90678543551991072096879203)
  ·
    refine ⟨136017815327986608145318805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90678543551991072096879203 136017815327986608145318805)
    ·
      refine ⟨6375835093499372256811819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 136017815327986608145318805 6375835093499372256811819)
      ·
        refine ⟨9563752640249058385217729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6375835093499372256811819 9563752640249058385217729)
        ·
          refine ⟨7172814480186793788913297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9563752640249058385217729 7172814480186793788913297)
          ·
            refine ⟨5379610860140095341684973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7172814480186793788913297 5379610860140095341684973)
            ·
              refine ⟨2017354072552535753131865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5379610860140095341684973 2017354072552535753131865)
              ·
                refine ⟨1513015554414401814848899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2017354072552535753131865 1513015554414401814848899)
                ·
                  refine ⟨2269523331621602722273349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1513015554414401814848899 2269523331621602722273349)
                  ·
                    refine ⟨425535624679050510426253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2269523331621602722273349 425535624679050510426253)
                    ·
                      rfl

theorem cell23_2486183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_2486183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486183 prefixEnd_2486183 := by exact prefixLift 2486183
  have htrace : WordTrace (prefixWord ++ tailWord_2486183) baseStart_2486183 baseEnd_2486183 := by
    simpa [prefixWord, tailWord_2486183, baseEnd_2486183] using wordTrace_append hprefix tailTrace_2486183
  have hstable : (prefixWord ++ tailWord_2486183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486183).length < 2 ^ (prefixWord ++ tailWord_2486183).sum := by decide
  have hdescent : baseEnd_2486183 < baseStart_2486183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486196 : List Nat := [2, 5, 2, 1, 2, 1, 1, 3, 6]
def baseStart_2486196 : Nat := 118140960795 + 2486196 * 2 ^ 59
def prefixEnd_2486196 : Nat := 4983230072969 + 3 ^ 40 * 2486196 * 2
def baseEnd_2486196 : Nat := 141845949920628886712911

theorem tailTrace_2486196 : CollatzResearch.WordTrace tailWord_2486196 prefixEnd_2486196 141845949920628886712911 := by
  unfold tailWord_2486196
  simp only [CollatzResearch.WordTrace]
  refine ⟨45339508850471987658551221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60452678467295983544734961 45339508850471987658551221)
  ·
    refine ⟨4250578954731748842989177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45339508850471987658551221 4250578954731748842989177)
    ·
      refine ⟨3187934216048811632241883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4250578954731748842989177 3187934216048811632241883)
      ·
        refine ⟨4781901324073217448362825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3187934216048811632241883 4781901324073217448362825)
        ·
          refine ⟨3586425993054913086272119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4781901324073217448362825 3586425993054913086272119)
          ·
            refine ⟨5379638989582369629408179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3586425993054913086272119 5379638989582369629408179)
            ·
              refine ⟨8069458484373554444112269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5379638989582369629408179 8069458484373554444112269)
              ·
                refine ⟨3026046931640082916542101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8069458484373554444112269 3026046931640082916542101)
                ·
                  refine ⟨141845949920628886712911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3026046931640082916542101 141845949920628886712911)
                  ·
                    rfl

theorem cell23_2486196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_2486196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486196 prefixEnd_2486196 := by exact prefixLift 2486196
  have htrace : WordTrace (prefixWord ++ tailWord_2486196) baseStart_2486196 baseEnd_2486196 := by
    simpa [prefixWord, tailWord_2486196, baseEnd_2486196] using wordTrace_append hprefix tailTrace_2486196
  have hstable : (prefixWord ++ tailWord_2486196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486196).length < 2 ^ (prefixWord ++ tailWord_2486196).sum := by decide
  have hdescent : baseEnd_2486196 < baseStart_2486196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486216 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 2, 3, 2]
def baseStart_2486216 : Nat := 118140960795 + 2486216 * 2 ^ 59
def prefixEnd_2486216 : Nat := 4983230072969 + 3 ^ 40 * 2486216 * 2
def baseEnd_2486216 : Nat := 1276623818898749902166107

theorem tailTrace_2486216 : CollatzResearch.WordTrace tailWord_2486216 prefixEnd_2486216 1276623818898749902166107 := by
  unfold tailWord_2486216
  simp only [CollatzResearch.WordTrace]
  refine ⟨45339873580435759366415251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60453164773914345821887001 45339873580435759366415251)
  ·
    refine ⟨68009810370653639049622877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45339873580435759366415251 68009810370653639049622877)
    ·
      refine ⟨25503678888995114643608579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68009810370653639049622877 25503678888995114643608579)
      ·
        refine ⟨38255518333492671965412869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25503678888995114643608579 38255518333492671965412869)
        ·
          refine ⟨7172909687529875993514913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38255518333492671965412869 7172909687529875993514913)
          ·
            refine ⟨5379682265647406995136185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7172909687529875993514913 5379682265647406995136185)
            ·
              refine ⟨4034761699235555246352139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5379682265647406995136185 4034761699235555246352139)
              ·
                refine ⟨6052142548853332869528209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4034761699235555246352139 6052142548853332869528209)
                ·
                  refine ⟨4539106911639999652146157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6052142548853332869528209 4539106911639999652146157)
                  ·
                    refine ⟨1702165091864999869554809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4539106911639999652146157 1702165091864999869554809)
                    ·
                      refine ⟨1276623818898749902166107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1702165091864999869554809 1276623818898749902166107)
                      ·
                        rfl

theorem cell23_2486216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_2486216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486216 prefixEnd_2486216 := by exact prefixLift 2486216
  have htrace : WordTrace (prefixWord ++ tailWord_2486216) baseStart_2486216 baseEnd_2486216 := by
    simpa [prefixWord, tailWord_2486216, baseEnd_2486216] using wordTrace_append hprefix tailTrace_2486216
  have hstable : (prefixWord ++ tailWord_2486216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486216).length < 2 ^ (prefixWord ++ tailWord_2486216).sum := by decide
  have hdescent : baseEnd_2486216 < baseStart_2486216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486222 : List Nat := [4, 1, 1, 1, 2, 2, 3, 2, 1, 6]
def baseStart_2486222 : Nat := 118140960795 + 2486222 * 2 ^ 59
def prefixEnd_2486222 : Nat := 4983230072969 + 3 ^ 40 * 2486222 * 2
def baseEnd_2486222 : Nat := 425542299927558959563693

theorem tailTrace_2486222 : CollatzResearch.WordTrace tailWord_2486222 prefixEnd_2486222 425542299927558959563693 := by
  unfold tailWord_2486222
  simp only [CollatzResearch.WordTrace]
  refine ⟨11334995749856222719693615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60453310665899854505032613 11334995749856222719693615)
  ·
    refine ⟨17002493624784334079540423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11334995749856222719693615 17002493624784334079540423)
    ·
      refine ⟨25503740437176501119310635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17002493624784334079540423 25503740437176501119310635)
      ·
        refine ⟨38255610655764751678965953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25503740437176501119310635 38255610655764751678965953)
        ·
          refine ⟨28691707991823563759224465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38255610655764751678965953 28691707991823563759224465)
          ·
            refine ⟨21518780993867672819418349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28691707991823563759224465 21518780993867672819418349)
            ·
              refine ⟨8069542872700377307281881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21518780993867672819418349 8069542872700377307281881)
              ·
                refine ⟨6052157154525282980461411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8069542872700377307281881 6052157154525282980461411)
                ·
                  refine ⟨9078235731787924470692117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6052157154525282980461411 9078235731787924470692117)
                  ·
                    refine ⟨425542299927558959563693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9078235731787924470692117 425542299927558959563693)
                    ·
                      rfl

theorem cell23_2486222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_2486222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486222 prefixEnd_2486222 := by exact prefixLift 2486222
  have htrace : WordTrace (prefixWord ++ tailWord_2486222) baseStart_2486222 baseEnd_2486222 := by
    simpa [prefixWord, tailWord_2486222, baseEnd_2486222] using wordTrace_append hprefix tailTrace_2486222
  have hstable : (prefixWord ++ tailWord_2486222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486222).length < 2 ^ (prefixWord ++ tailWord_2486222).sum := by decide
  have hdescent : baseEnd_2486222 < baseStart_2486222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486225 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 3, 1, 6]
def baseStart_2486225 : Nat := 118140960795 + 2486225 * 2 ^ 59
def prefixEnd_2486225 : Nat := 4983230072969 + 3 ^ 40 * 2486225 * 2
def baseEnd_2486225 : Nat := 1276628440224640366953565

theorem tailTrace_2486225 : CollatzResearch.WordTrace tailWord_2486225 prefixEnd_2486225 1276628440224640366953565 := by
  unfold tailWord_2486225
  simp only [CollatzResearch.WordTrace]
  refine ⟨90680075417838913269908129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60453383611892608846605419 90680075417838913269908129)
  ·
    refine ⟨68010056563379184952431097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90680075417838913269908129 68010056563379184952431097)
    ·
      refine ⟨51007542422534388714323323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68010056563379184952431097 51007542422534388714323323)
      ·
        refine ⟨76511313633801583071484985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51007542422534388714323323 76511313633801583071484985)
        ·
          refine ⟨57383485225351187303613739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76511313633801583071484985 57383485225351187303613739)
          ·
            refine ⟨86075227838026780955420609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57383485225351187303613739 86075227838026780955420609)
            ·
              refine ⟨64556420878520085716565457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86075227838026780955420609 64556420878520085716565457)
              ·
                refine ⟨48417315658890064287424093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64556420878520085716565457 48417315658890064287424093)
                ·
                  refine ⟨18156493372083774107784035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48417315658890064287424093 18156493372083774107784035)
                  ·
                    refine ⟨27234740058125661161676053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18156493372083774107784035 27234740058125661161676053)
                    ·
                      refine ⟨1276628440224640366953565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27234740058125661161676053 1276628440224640366953565)
                      ·
                        rfl

theorem cell23_2486225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 1, 6].length) (baseStart_2486225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486225 prefixEnd_2486225 := by exact prefixLift 2486225
  have htrace : WordTrace (prefixWord ++ tailWord_2486225) baseStart_2486225 baseEnd_2486225 := by
    simpa [prefixWord, tailWord_2486225, baseEnd_2486225] using wordTrace_append hprefix tailTrace_2486225
  have hstable : (prefixWord ++ tailWord_2486225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486225).length < 2 ^ (prefixWord ++ tailWord_2486225).sum := by decide
  have hdescent : baseEnd_2486225 < baseStart_2486225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486239 : List Nat := [1, 1, 2, 3, 4, 1, 1, 4, 2, 4]
def baseStart_2486239 : Nat := 118140960795 + 2486239 * 2 ^ 59
def prefixEnd_2486239 : Nat := 4983230072969 + 3 ^ 40 * 2486239 * 2
def baseEnd_2486239 : Nat := 425545209651267770726167

theorem tailTrace_2486239 : CollatzResearch.WordTrace tailWord_2486239 prefixEnd_2486239 425545209651267770726167 := by
  unfold tailWord_2486239
  simp only [CollatzResearch.WordTrace]
  refine ⟨90680586039788193660917771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60453724026525462440611847 90680586039788193660917771)
  ·
    refine ⟨136020879059682290491376657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90680586039788193660917771 136020879059682290491376657)
    ·
      refine ⟨102015659294761717868532493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136020879059682290491376657 102015659294761717868532493)
      ·
        refine ⟨38255872235535644200699685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102015659294761717868532493 38255872235535644200699685)
        ·
          refine ⟨7172976044162933287631191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38255872235535644200699685 7172976044162933287631191)
          ·
            refine ⟨10759464066244399931446787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7172976044162933287631191 10759464066244399931446787)
            ·
              refine ⟨16139196099366599897170181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10759464066244399931446787 16139196099366599897170181)
              ·
                refine ⟨3026099268631237480719409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16139196099366599897170181 3026099268631237480719409)
                ·
                  refine ⟨2269574451473428110539557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3026099268631237480719409 2269574451473428110539557)
                  ·
                    refine ⟨425545209651267770726167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2269574451473428110539557 425545209651267770726167)
                    ·
                      rfl

theorem cell23_2486239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 4].length) (baseStart_2486239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486239 prefixEnd_2486239 := by exact prefixLift 2486239
  have htrace : WordTrace (prefixWord ++ tailWord_2486239) baseStart_2486239 baseEnd_2486239 := by
    simpa [prefixWord, tailWord_2486239, baseEnd_2486239] using wordTrace_append hprefix tailTrace_2486239
  have hstable : (prefixWord ++ tailWord_2486239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486239).length < 2 ^ (prefixWord ++ tailWord_2486239).sum := by decide
  have hdescent : baseEnd_2486239 < baseStart_2486239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486279 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 3]
def baseStart_2486279 : Nat := 118140960795 + 2486279 * 2 ^ 59
def prefixEnd_2486279 : Nat := 4983230072969 + 3 ^ 40 * 2486279 * 2
def baseEnd_2486279 : Nat := 1276656168179983155678317

theorem tailTrace_2486279 : CollatzResearch.WordTrace tailWord_2486279 prefixEnd_2486279 1276656168179983155678317 := by
  unfold tailWord_2486279
  simp only [CollatzResearch.WordTrace]
  refine ⟨90682044959643280492373891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60454696639762186994915927 90682044959643280492373891)
  ·
    refine ⟨136023067439464920738560837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90682044959643280492373891 136023067439464920738560837)
    ·
      refine ⟨25504325144899672638480157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136023067439464920738560837 25504325144899672638480157)
      ·
        refine ⟨9564121929337377239430059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25504325144899672638480157 9564121929337377239430059)
        ·
          refine ⟨14346182894006065859145089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9564121929337377239430059 14346182894006065859145089)
          ·
            refine ⟨10759637170504549394358817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14346182894006065859145089 10759637170504549394358817)
            ·
              refine ⟨8069727877878412045769113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10759637170504549394358817 8069727877878412045769113)
              ·
                refine ⟨6052295908408809034326835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8069727877878412045769113 6052295908408809034326835)
                ·
                  refine ⟨9078443862613213551490253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6052295908408809034326835 9078443862613213551490253)
                  ·
                    refine ⟨3404416448479955081808845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9078443862613213551490253 3404416448479955081808845)
                    ·
                      refine ⟨1276656168179983155678317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3404416448479955081808845 1276656168179983155678317)
                      ·
                        rfl

theorem cell23_2486279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_2486279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486279 prefixEnd_2486279 := by exact prefixLift 2486279
  have htrace : WordTrace (prefixWord ++ tailWord_2486279) baseStart_2486279 baseEnd_2486279 := by
    simpa [prefixWord, tailWord_2486279, baseEnd_2486279] using wordTrace_append hprefix tailTrace_2486279
  have hstable : (prefixWord ++ tailWord_2486279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486279).length < 2 ^ (prefixWord ++ tailWord_2486279).sum := by decide
  have hdescent : baseEnd_2486279 < baseStart_2486279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486319 : List Nat := [1, 1, 2, 1, 2, 1, 1, 7, 1, 4, 2]
def baseStart_2486319 : Nat := 118140960795 + 2486319 * 2 ^ 59
def prefixEnd_2486319 : Nat := 4983230072969 + 3 ^ 40 * 2486319 * 2
def baseEnd_2486319 : Nat := 1276676707406162999178133

theorem tailTrace_2486319 : CollatzResearch.WordTrace tailWord_2486319 prefixEnd_2486319 1276676707406162999178133 := by
  unfold tailWord_2486319
  simp only [CollatzResearch.WordTrace]
  refine ⟨90683503879498367323830011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60455669252998911549220007 90683503879498367323830011)
  ·
    refine ⟨136025255819247550985745017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90683503879498367323830011 136025255819247550985745017)
    ·
      refine ⟨102018941864435663239308763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136025255819247550985745017 102018941864435663239308763)
      ·
        refine ⟨153028412796653494858963145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102018941864435663239308763 153028412796653494858963145)
        ·
          refine ⟨114771309597490121144222359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153028412796653494858963145 114771309597490121144222359)
          ·
            refine ⟨172156964396235181716333539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114771309597490121144222359 172156964396235181716333539)
            ·
              refine ⟨258235446594352772574500309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172156964396235181716333539 258235446594352772574500309)
              ·
                refine ⟨6052393279555143107214851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 258235446594352772574500309 6052393279555143107214851)
                ·
                  refine ⟨9078589919332714660822277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6052393279555143107214851 9078589919332714660822277)
                  ·
                    refine ⟨1702235609874883998904177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9078589919332714660822277 1702235609874883998904177)
                    ·
                      refine ⟨1276676707406162999178133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1702235609874883998904177 1276676707406162999178133)
                      ·
                        rfl

theorem cell23_2486319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 4, 2].length) (baseStart_2486319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486319 prefixEnd_2486319 := by exact prefixLift 2486319
  have htrace : WordTrace (prefixWord ++ tailWord_2486319) baseStart_2486319 baseEnd_2486319 := by
    simpa [prefixWord, tailWord_2486319, baseEnd_2486319] using wordTrace_append hprefix tailTrace_2486319
  have hstable : (prefixWord ++ tailWord_2486319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486319).length < 2 ^ (prefixWord ++ tailWord_2486319).sum := by decide
  have hdescent : baseEnd_2486319 < baseStart_2486319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486336 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 4, 2, 2]
def baseStart_2486336 : Nat := 118140960795 + 2486336 * 2 ^ 59
def prefixEnd_2486336 : Nat := 4983230072969 + 3 ^ 40 * 2486336 * 2
def baseEnd_2486336 : Nat := 1276685436577289432665555

theorem tailTrace_2486336 : CollatzResearch.WordTrace tailWord_2486336 prefixEnd_2486336 1276685436577289432665555 := by
  unfold tailWord_2486336
  simp only [CollatzResearch.WordTrace]
  refine ⟨45342061960218389613599431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60456082613624519484799241 45342061960218389613599431)
  ·
    refine ⟨68013092940327584420399147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45342061960218389613599431 68013092940327584420399147)
    ·
      refine ⟨102019639410491376630598721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68013092940327584420399147 102019639410491376630598721)
      ·
        refine ⟨76514729557868532472949041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102019639410491376630598721 76514729557868532472949041)
        ·
          refine ⟨57386047168401399354711781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76514729557868532472949041 57386047168401399354711781)
          ·
            refine ⟨10759883844075262379008459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57386047168401399354711781 10759883844075262379008459)
            ·
              refine ⟨16139825766112893568512689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10759883844075262379008459 16139825766112893568512689)
              ·
                refine ⟨12104869324584670176384517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16139825766112893568512689 12104869324584670176384517)
                ·
                  refine ⟨2269662998359625658072097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12104869324584670176384517 2269662998359625658072097)
                  ·
                    refine ⟨1702247248769719243554073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2269662998359625658072097 1702247248769719243554073)
                    ·
                      refine ⟨1276685436577289432665555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1702247248769719243554073 1276685436577289432665555)
                      ·
                        rfl

theorem cell23_2486336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 4, 2, 2].length) (baseStart_2486336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486336 prefixEnd_2486336 := by exact prefixLift 2486336
  have htrace : WordTrace (prefixWord ++ tailWord_2486336) baseStart_2486336 baseEnd_2486336 := by
    simpa [prefixWord, tailWord_2486336, baseEnd_2486336] using wordTrace_append hprefix tailTrace_2486336
  have hstable : (prefixWord ++ tailWord_2486336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486336).length < 2 ^ (prefixWord ++ tailWord_2486336).sum := by decide
  have hdescent : baseEnd_2486336 < baseStart_2486336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486359 : List Nat := [1, 1, 3, 2, 2, 1, 2, 6, 5]
def baseStart_2486359 : Nat := 118140960795 + 2486359 * 2 ^ 59
def prefixEnd_2486359 : Nat := 4983230072969 + 3 ^ 40 * 2486359 * 2
def baseEnd_2486359 : Nat := 141855249625815871408661

theorem tailTrace_2486359 : CollatzResearch.WordTrace tailWord_2486359 prefixEnd_2486359 141855249625815871408661 := by
  unfold tailWord_2486359
  simp only [CollatzResearch.WordTrace]
  refine ⟨90684962799353454155286131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60456641866235636103524087 90684962799353454155286131)
  ·
    refine ⟨136027444199030181232929197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90684962799353454155286131 136027444199030181232929197)
    ·
      refine ⟨51010291574636317962348449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136027444199030181232929197 51010291574636317962348449)
      ·
        refine ⟨38257718680977238471761337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51010291574636317962348449 38257718680977238471761337)
        ·
          refine ⟨28693289010732928853821003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38257718680977238471761337 28693289010732928853821003)
          ·
            refine ⟨43039933516099393280731505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28693289010732928853821003 43039933516099393280731505)
            ·
              refine ⟨32279950137074544960548629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43039933516099393280731505 32279950137074544960548629)
              ·
                refine ⟨1513122662675369295025717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 32279950137074544960548629 1513122662675369295025717)
                ·
                  refine ⟨141855249625815871408661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1513122662675369295025717 141855249625815871408661)
                  ·
                    rfl

theorem cell23_2486359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 6, 5].length) (baseStart_2486359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486359 prefixEnd_2486359 := by exact prefixLift 2486359
  have htrace : WordTrace (prefixWord ++ tailWord_2486359) baseStart_2486359 baseEnd_2486359 := by
    simpa [prefixWord, tailWord_2486359, baseEnd_2486359] using wordTrace_append hprefix tailTrace_2486359
  have hstable : (prefixWord ++ tailWord_2486359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486359).length < 2 ^ (prefixWord ++ tailWord_2486359).sum := by decide
  have hdescent : baseEnd_2486359 < baseStart_2486359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486372 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 3, 7]
def baseStart_2486372 : Nat := 118140960795 + 2486372 * 2 ^ 59
def prefixEnd_2486372 : Nat := 4983230072969 + 3 ^ 40 * 2486372 * 2
def baseEnd_2486372 : Nat := 425567973960283763938463

theorem tailTrace_2486372 : CollatzResearch.WordTrace tailWord_2486372 prefixEnd_2486372 425567973960283763938463 := by
  unfold tailWord_2486372
  simp only [CollatzResearch.WordTrace]
  refine ⟨45342718474153178687754685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60456957965537571583672913 45342718474153178687754685)
  ·
    refine ⟨17003519427807442007908007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45342718474153178687754685 17003519427807442007908007)
    ·
      refine ⟨25505279141711163011862011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17003519427807442007908007 25505279141711163011862011)
      ·
        refine ⟨38257918712566744517793017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25505279141711163011862011 38257918712566744517793017)
        ·
          refine ⟨28693439034425058388344763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38257918712566744517793017 28693439034425058388344763)
          ·
            refine ⟨43040158551637587582517145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28693439034425058388344763 43040158551637587582517145)
            ·
              refine ⟨32280118913728190686887859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43040158551637587582517145 32280118913728190686887859)
              ·
                refine ⟨48420178370592286030331789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32280118913728190686887859 48420178370592286030331789)
                ·
                  refine ⟨18157566888972107261374421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48420178370592286030331789 18157566888972107261374421)
                  ·
                    refine ⟨425567973960283763938463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18157566888972107261374421 425567973960283763938463)
                    ·
                      rfl

theorem cell23_2486372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_2486372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486372 prefixEnd_2486372 := by exact prefixLift 2486372
  have htrace : WordTrace (prefixWord ++ tailWord_2486372) baseStart_2486372 baseEnd_2486372 := by
    simpa [prefixWord, tailWord_2486372, baseEnd_2486372] using wordTrace_append hprefix tailTrace_2486372
  have hstable : (prefixWord ++ tailWord_2486372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486372).length < 2 ^ (prefixWord ++ tailWord_2486372).sum := by decide
  have hdescent : baseEnd_2486372 < baseStart_2486372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486409 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 2, 1, 4]
def baseStart_2486409 : Nat := 118140960795 + 2486409 * 2 ^ 59
def prefixEnd_2486409 : Nat := 4983230072969 + 3 ^ 40 * 2486409 * 2
def baseEnd_2486409 : Nat := 1276722920665067647052719

theorem tailTrace_2486409 : CollatzResearch.WordTrace tailWord_2486409 prefixEnd_2486409 1276722920665067647052719 := by
  unfold tailWord_2486409
  simp only [CollatzResearch.WordTrace]
  refine ⟨90686786449172312694606281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60457857632781541796404187 90686786449172312694606281)
  ·
    refine ⟨68015089836879234520954711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90686786449172312694606281 68015089836879234520954711)
    ·
      refine ⟨102022634755318851781432067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68015089836879234520954711 102022634755318851781432067)
      ·
        refine ⟨153033952132978277672148101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102022634755318851781432067 153033952132978277672148101)
        ·
          refine ⟨28693866024933427063527769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153033952132978277672148101 28693866024933427063527769)
          ·
            refine ⟨21520399518700070297645827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28693866024933427063527769 21520399518700070297645827)
            ·
              refine ⟨32280599278050105446468741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21520399518700070297645827 32280599278050105446468741)
              ·
                refine ⟨6052612364634394771212889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32280599278050105446468741 6052612364634394771212889)
                ·
                  refine ⟨4539459273475796078409667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6052612364634394771212889 4539459273475796078409667)
                  ·
                    refine ⟨6809188910213694117614501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4539459273475796078409667 6809188910213694117614501)
                    ·
                      refine ⟨1276722920665067647052719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6809188910213694117614501 1276722920665067647052719)
                      ·
                        rfl

theorem cell23_2486409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 1, 4].length) (baseStart_2486409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486409 prefixEnd_2486409 := by exact prefixLift 2486409
  have htrace : WordTrace (prefixWord ++ tailWord_2486409) baseStart_2486409 baseEnd_2486409 := by
    simpa [prefixWord, tailWord_2486409, baseEnd_2486409] using wordTrace_append hprefix tailTrace_2486409
  have hstable : (prefixWord ++ tailWord_2486409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486409).length < 2 ^ (prefixWord ++ tailWord_2486409).sum := by decide
  have hdescent : baseEnd_2486409 < baseStart_2486409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486419 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 3, 4]
def baseStart_2486419 : Nat := 118140960795 + 2486419 * 2 ^ 59
def prefixEnd_2486419 : Nat := 4983230072969 + 3 ^ 40 * 2486419 * 2
def baseEnd_2486419 : Nat := 425576018490537535975891

theorem tailTrace_2486419 : CollatzResearch.WordTrace tailWord_2486419 prefixEnd_2486419 425576018490537535975891 := by
  unfold tailWord_2486419
  simp only [CollatzResearch.WordTrace]
  refine ⟨90687151179136084402470311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60458100786090722934980207 90687151179136084402470311)
  ·
    refine ⟨136030726768704126603705467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90687151179136084402470311 136030726768704126603705467)
    ·
      refine ⟨204046090153056189905558201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136030726768704126603705467 204046090153056189905558201)
      ·
        refine ⟨153034567614792142429168651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204046090153056189905558201 153034567614792142429168651)
        ·
          refine ⟨229551851422188213643752977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153034567614792142429168651 229551851422188213643752977)
          ·
            refine ⟨172163888566641160232814733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229551851422188213643752977 172163888566641160232814733)
            ·
              refine ⟨64561458212490435087305525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172163888566641160232814733 64561458212490435087305525)
              ·
                refine ⟨6052636707420978289434893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64561458212490435087305525 6052636707420978289434893)
                ·
                  refine ⟨2269738765282866858538085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6052636707420978289434893 2269738765282866858538085)
                  ·
                    refine ⟨425576018490537535975891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2269738765282866858538085 425576018490537535975891)
                    ·
                      rfl

theorem cell23_2486419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 4].length) (baseStart_2486419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486419 prefixEnd_2486419 := by exact prefixLift 2486419
  have htrace : WordTrace (prefixWord ++ tailWord_2486419) baseStart_2486419 baseEnd_2486419 := by
    simpa [prefixWord, tailWord_2486419, baseEnd_2486419] using wordTrace_append hprefix tailTrace_2486419
  have hstable : (prefixWord ++ tailWord_2486419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486419).length < 2 ^ (prefixWord ++ tailWord_2486419).sum := by decide
  have hdescent : baseEnd_2486419 < baseStart_2486419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486496 : List Nat := [2, 1, 1, 3, 1, 3, 4, 2, 1, 5]
def baseStart_2486496 : Nat := 118140960795 + 2486496 * 2 ^ 59
def prefixEnd_2486496 : Nat := 4983230072969 + 3 ^ 40 * 2486496 * 2
def baseEnd_2486496 : Nat := 425589197827336268888273

theorem tailTrace_2486496 : CollatzResearch.WordTrace tailWord_2486496 prefixEnd_2486496 425589197827336268888273 := by
  unfold tailWord_2486496
  simp only [CollatzResearch.WordTrace]
  refine ⟨45344979799928563276511671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60459973066571417702015561 45344979799928563276511671)
  ·
    refine ⟨68017469699892844914767507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45344979799928563276511671 68017469699892844914767507)
    ·
      refine ⟨102026204549839267372151261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68017469699892844914767507 102026204549839267372151261)
      ·
        refine ⟨38259826706189725264556723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102026204549839267372151261 38259826706189725264556723)
        ·
          refine ⟨57389740059284587896835085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38259826706189725264556723 57389740059284587896835085)
          ·
            refine ⟨21521152522231720461313157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57389740059284587896835085 21521152522231720461313157)
            ·
              refine ⟨4035216097918447586496217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21521152522231720461313157 4035216097918447586496217)
              ·
                refine ⟨3026412073438835689872163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4035216097918447586496217 3026412073438835689872163)
                ·
                  refine ⟨4539618110158253534808245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3026412073438835689872163 4539618110158253534808245)
                  ·
                    refine ⟨425589197827336268888273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4539618110158253534808245 425589197827336268888273)
                    ·
                      rfl

theorem cell23_2486496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 1, 5].length) (baseStart_2486496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486496 prefixEnd_2486496 := by exact prefixLift 2486496
  have htrace : WordTrace (prefixWord ++ tailWord_2486496) baseStart_2486496 baseEnd_2486496 := by
    simpa [prefixWord, tailWord_2486496, baseEnd_2486496] using wordTrace_append hprefix tailTrace_2486496
  have hstable : (prefixWord ++ tailWord_2486496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486496).length < 2 ^ (prefixWord ++ tailWord_2486496).sum := by decide
  have hdescent : baseEnd_2486496 < baseStart_2486496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486503 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 1, 5, 2]
def baseStart_2486503 : Nat := 118140960795 + 2486503 * 2 ^ 59
def prefixEnd_2486503 : Nat := 4983230072969 + 3 ^ 40 * 2486503 * 2
def baseEnd_2486503 : Nat := 1276771187846590279277287

theorem tailTrace_2486503 : CollatzResearch.WordTrace tailWord_2486503 prefixEnd_2486503 1276771187846590279277287 := by
  unfold tailWord_2486503
  simp only [CollatzResearch.WordTrace]
  refine ⟨90690214910831766748528163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60460143273887844499018775 90690214910831766748528163)
  ·
    refine ⟨136035322366247650122792245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90690214910831766748528163 136035322366247650122792245)
    ·
      refine ⟨12753311471835717199011773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136035322366247650122792245 12753311471835717199011773)
      ·
        refine ⟨4782491801938393949629415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12753311471835717199011773 4782491801938393949629415)
        ·
          refine ⟨7173737702907590924444123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4782491801938393949629415 7173737702907590924444123)
          ·
            refine ⟨10760606554361386386666185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7173737702907590924444123 10760606554361386386666185)
            ·
              refine ⟨8070454915771039789999639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10760606554361386386666185 8070454915771039789999639)
              ·
                refine ⟨12105682373656559684999459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8070454915771039789999639 12105682373656559684999459)
                ·
                  refine ⟨18158523560484839527499189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12105682373656559684999459 18158523560484839527499189)
                  ·
                    refine ⟨1702361583795453705703049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18158523560484839527499189 1702361583795453705703049)
                    ·
                      refine ⟨1276771187846590279277287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1702361583795453705703049 1276771187846590279277287)
                      ·
                        rfl

theorem cell23_2486503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_2486503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486503 prefixEnd_2486503 := by exact prefixLift 2486503
  have htrace : WordTrace (prefixWord ++ tailWord_2486503) baseStart_2486503 baseEnd_2486503 := by
    simpa [prefixWord, tailWord_2486503, baseEnd_2486503] using wordTrace_append hprefix tailTrace_2486503
  have hstable : (prefixWord ++ tailWord_2486503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486503).length < 2 ^ (prefixWord ++ tailWord_2486503).sum := by decide
  have hdescent : baseEnd_2486503 < baseStart_2486503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486529 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 3, 1, 6]
def baseStart_2486529 : Nat := 118140960795 + 2486529 * 2 ^ 59
def prefixEnd_2486529 : Nat := 4983230072969 + 3 ^ 40 * 2486529 * 2
def baseEnd_2486529 : Nat := 1276784538343607177552167

theorem tailTrace_2486529 : CollatzResearch.WordTrace tailWord_2486529 prefixEnd_2486529 1276784538343607177552167 := by
  unfold tailWord_2486529
  simp only [CollatzResearch.WordTrace]
  refine ⟨90691163208737573188974641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60460775472491715459316427 90691163208737573188974641)
  ·
    refine ⟨68018372406553179891730981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90691163208737573188974641 68018372406553179891730981)
    ·
      refine ⟨12753444826228721229699559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68018372406553179891730981 12753444826228721229699559)
      ·
        refine ⟨19130167239343081844549339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12753444826228721229699559 19130167239343081844549339)
        ·
          refine ⟨28695250859014622766824009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19130167239343081844549339 28695250859014622766824009)
          ·
            refine ⟨21521438144260967075118007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28695250859014622766824009 21521438144260967075118007)
            ·
              refine ⟨32282157216391450612677011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21521438144260967075118007 32282157216391450612677011)
              ·
                refine ⟨48423235824587175919015517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32282157216391450612677011 48423235824587175919015517)
                ·
                  refine ⟨18158713434220190969630819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48423235824587175919015517 18158713434220190969630819)
                  ·
                    refine ⟨27238070151330286454446229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18158713434220190969630819 27238070151330286454446229)
                    ·
                      refine ⟨1276784538343607177552167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27238070151330286454446229 1276784538343607177552167)
                      ·
                        rfl

theorem cell23_2486529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_2486529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486529 prefixEnd_2486529 := by exact prefixLift 2486529
  have htrace : WordTrace (prefixWord ++ tailWord_2486529) baseStart_2486529 baseEnd_2486529 := by
    simpa [prefixWord, tailWord_2486529, baseEnd_2486529] using wordTrace_append hprefix tailTrace_2486529
  have hstable : (prefixWord ++ tailWord_2486529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486529).length < 2 ^ (prefixWord ++ tailWord_2486529).sum := by decide
  have hdescent : baseEnd_2486529 < baseStart_2486529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486533 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 3, 2, 2]
def baseStart_2486533 : Nat := 118140960795 + 2486533 * 2 ^ 59
def prefixEnd_2486533 : Nat := 4983230072969 + 3 ^ 40 * 2486533 * 2
def baseEnd_2486533 : Nat := 1276786592266225161902149

theorem tailTrace_2486533 : CollatzResearch.WordTrace tailWord_2486533 prefixEnd_2486533 1276786592266225161902149 := by
  unfold tailWord_2486533
  simp only [CollatzResearch.WordTrace]
  refine ⟨90691309100723081872120253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60460872733815387914746835 90691309100723081872120253)
  ·
    refine ⟨34009240912771155702045095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90691309100723081872120253 34009240912771155702045095)
    ·
      refine ⟨51013861369156733553067643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34009240912771155702045095 51013861369156733553067643)
      ·
        refine ⟨76520792053735100329601465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51013861369156733553067643 76520792053735100329601465)
        ·
          refine ⟨57390594040301325247201099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76520792053735100329601465 57390594040301325247201099)
          ·
            refine ⟨86085891060451987870801649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57390594040301325247201099 86085891060451987870801649)
            ·
              refine ⟨64564418295338990903101237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86085891060451987870801649 64564418295338990903101237)
              ·
                refine ⟨6052914215188030397165741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 64564418295338990903101237 6052914215188030397165741)
                ·
                  refine ⟨2269842830695511398937153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6052914215188030397165741 2269842830695511398937153)
                  ·
                    refine ⟨1702382123021633549202865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2269842830695511398937153 1702382123021633549202865)
                    ·
                      refine ⟨1276786592266225161902149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1702382123021633549202865 1276786592266225161902149)
                      ·
                        rfl

theorem cell23_2486533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 3, 2, 2].length) (baseStart_2486533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486533 prefixEnd_2486533 := by exact prefixLift 2486533
  have htrace : WordTrace (prefixWord ++ tailWord_2486533) baseStart_2486533 baseEnd_2486533 := by
    simpa [prefixWord, tailWord_2486533, baseEnd_2486533] using wordTrace_append hprefix tailTrace_2486533
  have hstable : (prefixWord ++ tailWord_2486533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486533).length < 2 ^ (prefixWord ++ tailWord_2486533).sum := by decide
  have hdescent : baseEnd_2486533 < baseStart_2486533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486536 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_2486536 : Nat := 118140960795 + 2486536 * 2 ^ 59
def prefixEnd_2486536 : Nat := 4983230072969 + 3 ^ 40 * 2486536 * 2
def baseEnd_2486536 : Nat := 1276788132708188650164635

theorem tailTrace_2486536 : CollatzResearch.WordTrace tailWord_2486536 prefixEnd_2486536 1276788132708188650164635 := by
  unfold tailWord_2486536
  simp only [CollatzResearch.WordTrace]
  refine ⟨45345709259856106692239731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60460945679808142256319641 45345709259856106692239731)
  ·
    refine ⟨68018563889784160038359597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45345709259856106692239731 68018563889784160038359597)
    ·
      refine ⟨25506961458669060014384849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68018563889784160038359597 25506961458669060014384849)
      ·
        refine ⟨19130221094001795010788637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25506961458669060014384849 19130221094001795010788637)
        ·
          refine ⟨7173832910250673129045739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19130221094001795010788637 7173832910250673129045739)
          ·
            refine ⟨10760749365376009693568609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7173832910250673129045739 10760749365376009693568609)
            ·
              refine ⟨8070562024032007270176457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10760749365376009693568609 8070562024032007270176457)
              ·
                refine ⟨6052921518024005452632343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8070562024032007270176457 6052921518024005452632343)
                ·
                  refine ⟨9079382277036008178948515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6052921518024005452632343 9079382277036008178948515)
                  ·
                    refine ⟨13619073415554012268422773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9079382277036008178948515 13619073415554012268422773)
                    ·
                      refine ⟨1276788132708188650164635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13619073415554012268422773 1276788132708188650164635)
                      ·
                        rfl

theorem cell23_2486536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_2486536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486536 prefixEnd_2486536 := by exact prefixLift 2486536
  have htrace : WordTrace (prefixWord ++ tailWord_2486536) baseStart_2486536 baseEnd_2486536 := by
    simpa [prefixWord, tailWord_2486536, baseEnd_2486536] using wordTrace_append hprefix tailTrace_2486536
  have hstable : (prefixWord ++ tailWord_2486536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486536).length < 2 ^ (prefixWord ++ tailWord_2486536).sum := by decide
  have hdescent : baseEnd_2486536 < baseStart_2486536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486539 : List Nat := [1, 1, 1, 1, 5, 2, 4, 8]
def baseStart_2486539 : Nat := 118140960795 + 2486539 * 2 ^ 59
def prefixEnd_2486539 : Nat := 4983230072969 + 3 ^ 40 * 2486539 * 2
def baseEnd_2486539 : Nat := 47288506412968597719523

theorem tailTrace_2486539 : CollatzResearch.WordTrace tailWord_2486539 prefixEnd_2486539 47288506412968597719523 := by
  unfold tailWord_2486539
  simp only [CollatzResearch.WordTrace]
  refine ⟨90691527938701344896838671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60461018625800896597892447 90691527938701344896838671)
  ·
    refine ⟨136037291908052017345258007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90691527938701344896838671 136037291908052017345258007)
    ·
      refine ⟨204055937862078026017887011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136037291908052017345258007 204055937862078026017887011)
      ·
        refine ⟨306083906793117039026830517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204055937862078026017887011 306083906793117039026830517)
        ·
          refine ⟨28695366261854722408765361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 306083906793117039026830517 28695366261854722408765361)
          ·
            refine ⟨21521524696391041806574021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28695366261854722408765361 21521524696391041806574021)
            ·
              refine ⟨4035285880573320338732629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21521524696391041806574021 4035285880573320338732629)
              ·
                refine ⟨47288506412968597719523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4035285880573320338732629 47288506412968597719523)
                ·
                  rfl

theorem cell23_2486539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 8].length) (baseStart_2486539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486539 prefixEnd_2486539 := by exact prefixLift 2486539
  have htrace : WordTrace (prefixWord ++ tailWord_2486539) baseStart_2486539 baseEnd_2486539 := by
    simpa [prefixWord, tailWord_2486539, baseEnd_2486539] using wordTrace_append hprefix tailTrace_2486539
  have hstable : (prefixWord ++ tailWord_2486539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486539).length < 2 ^ (prefixWord ++ tailWord_2486539).sum := by decide
  have hdescent : baseEnd_2486539 < baseStart_2486539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486570 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_2486570 : Nat := 118140960795 + 2486570 * 2 ^ 59
def prefixEnd_2486570 : Nat := 4983230072969 + 3 ^ 40 * 2486570 * 2
def baseEnd_2486570 : Nat := 1276805591050441517139479

theorem tailTrace_2486570 : CollatzResearch.WordTrace tailWord_2486570 prefixEnd_2486570 1276805591050441517139479 := by
  unfold tailWord_2486570
  simp only [CollatzResearch.WordTrace]
  refine ⟨22673164650397259297804291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60461772401059358127478109 22673164650397259297804291)
  ·
    refine ⟨34009746975595888946706437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22673164650397259297804291 34009746975595888946706437)
    ·
      refine ⟨6376827557924229177507457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34009746975595888946706437 6376827557924229177507457)
      ·
        refine ⟨4782620668443171883130593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6376827557924229177507457 4782620668443171883130593)
        ·
          refine ⟨3586965501332378912347945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4782620668443171883130593 3586965501332378912347945)
          ·
            refine ⟨2690224125999284184260959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3586965501332378912347945 2690224125999284184260959)
            ·
              refine ⟨4035336188998926276391439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2690224125999284184260959 4035336188998926276391439)
              ·
                refine ⟨6053004283498389414587159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4035336188998926276391439 6053004283498389414587159)
                ·
                  refine ⟨9079506425247584121880739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6053004283498389414587159 9079506425247584121880739)
                  ·
                    refine ⟨13619259637871376182821109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9079506425247584121880739 13619259637871376182821109)
                    ·
                      refine ⟨1276805591050441517139479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13619259637871376182821109 1276805591050441517139479)
                      ·
                        rfl

theorem cell23_2486570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_2486570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486570 prefixEnd_2486570 := by exact prefixLift 2486570
  have htrace : WordTrace (prefixWord ++ tailWord_2486570) baseStart_2486570 baseEnd_2486570 := by
    simpa [prefixWord, tailWord_2486570, baseEnd_2486570] using wordTrace_append hprefix tailTrace_2486570
  have hstable : (prefixWord ++ tailWord_2486570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486570).length < 2 ^ (prefixWord ++ tailWord_2486570).sum := by decide
  have hdescent : baseEnd_2486570 < baseStart_2486570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486573 : List Nat := [1, 5, 3, 1, 3, 10]
def baseStart_2486573 : Nat := 118140960795 + 2486573 * 2 ^ 59
def prefixEnd_2486573 : Nat := 4983230072969 + 3 ^ 40 * 2486573 * 2
def baseEnd_2486573 : Nat := 5254350335359691380255

theorem tailTrace_2486573 : CollatzResearch.WordTrace tailWord_2486573 prefixEnd_2486573 5254350335359691380255 := by
  unfold tailWord_2486573
  simp only [CollatzResearch.WordTrace]
  refine ⟨90692768020578168703576373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60461845347052112469050915 90692768020578168703576373)
  ·
    refine ⟨8502447001929203315960285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90692768020578168703576373 8502447001929203315960285)
    ·
      refine ⟨3188417625723451243485107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8502447001929203315960285 3188417625723451243485107)
      ·
        refine ⟨4782626438585176865227661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3188417625723451243485107 4782626438585176865227661)
        ·
          refine ⟨1793484914469441324460373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4782626438585176865227661 1793484914469441324460373)
          ·
            refine ⟨5254350335359691380255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1793484914469441324460373 5254350335359691380255)
            ·
              rfl

theorem cell23_2486573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 10].length) (baseStart_2486573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486573 prefixEnd_2486573 := by exact prefixLift 2486573
  have htrace : WordTrace (prefixWord ++ tailWord_2486573) baseStart_2486573 baseEnd_2486573 := by
    simpa [prefixWord, tailWord_2486573, baseEnd_2486573] using wordTrace_append hprefix tailTrace_2486573
  have hstable : (prefixWord ++ tailWord_2486573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486573).length < 2 ^ (prefixWord ++ tailWord_2486573).sum := by decide
  have hdescent : baseEnd_2486573 < baseStart_2486573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486623 : List Nat := [1, 1, 2, 3, 1, 2, 4, 2, 1, 4, 2]
def baseStart_2486623 : Nat := 118140960795 + 2486623 * 2 ^ 59
def prefixEnd_2486623 : Nat := 4983230072969 + 3 ^ 40 * 2486623 * 2
def baseEnd_2486623 : Nat := 1276832805525129809776735

theorem tailTrace_2486623 : CollatzResearch.WordTrace tailWord_2486623 prefixEnd_2486623 1276832805525129809776735 := by
  unfold tailWord_2486623
  simp only [CollatzResearch.WordTrace]
  refine ⟨90694591670397027242896523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60463061113598018161931015 90694591670397027242896523)
  ·
    refine ⟨136041887505595540864344785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90694591670397027242896523 136041887505595540864344785)
    ·
      refine ⟨102031415629196655648258589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136041887505595540864344785 102031415629196655648258589)
      ·
        refine ⟨38261780860948745868096971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102031415629196655648258589 38261780860948745868096971)
        ·
          refine ⟨57392671291423118802145457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38261780860948745868096971 57392671291423118802145457)
          ·
            refine ⟨43044503468567339101609093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57392671291423118802145457 43044503468567339101609093)
            ·
              refine ⟨8070844400356376081551705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43044503468567339101609093 8070844400356376081551705)
              ·
                refine ⟨6053133300267282061163779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8070844400356376081551705 6053133300267282061163779)
                ·
                  refine ⟨9079699950400923091745669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6053133300267282061163779 9079699950400923091745669)
                  ·
                    refine ⟨1702443740700173079702313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9079699950400923091745669 1702443740700173079702313)
                    ·
                      refine ⟨1276832805525129809776735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1702443740700173079702313 1276832805525129809776735)
                      ·
                        rfl

theorem cell23_2486623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_2486623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486623 prefixEnd_2486623 := by exact prefixLift 2486623
  have htrace : WordTrace (prefixWord ++ tailWord_2486623) baseStart_2486623 baseEnd_2486623 := by
    simpa [prefixWord, tailWord_2486623, baseEnd_2486623] using wordTrace_append hprefix tailTrace_2486623
  have hstable : (prefixWord ++ tailWord_2486623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486623).length < 2 ^ (prefixWord ++ tailWord_2486623).sum := by decide
  have hdescent : baseEnd_2486623 < baseStart_2486623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486639 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 9]
def baseStart_2486639 : Nat := 118140960795 + 2486639 * 2 ^ 59
def prefixEnd_2486639 : Nat := 4983230072969 + 3 ^ 40 * 2486639 * 2
def baseEnd_2486639 : Nat := 1276841021215601747176661

theorem tailTrace_2486639 : CollatzResearch.WordTrace tailWord_2486639 prefixEnd_2486639 1276841021215601747176661 := by
  unfold tailWord_2486639
  simp only [CollatzResearch.WordTrace]
  refine ⟨90695175238339061975478971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60463450158892707983652647 90695175238339061975478971)
  ·
    refine ⟨136042762857508592963218457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90695175238339061975478971 136042762857508592963218457)
    ·
      refine ⟨102032072143131444722413843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136042762857508592963218457 102032072143131444722413843)
      ·
        refine ⟨153048108214697167083620765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102032072143131444722413843 153048108214697167083620765)
        ·
          refine ⟨57393040580511437656357787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153048108214697167083620765 57393040580511437656357787)
          ·
            refine ⟨86089560870767156484536681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57393040580511437656357787 86089560870767156484536681)
            ·
              refine ⟨64567170653075367363402511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86089560870767156484536681 64567170653075367363402511)
              ·
                refine ⟨96850755979613051045103767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64567170653075367363402511 96850755979613051045103767)
                ·
                  refine ⟨145276133969419576567655651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96850755979613051045103767 145276133969419576567655651)
                  ·
                    refine ⟨217914200954129364851483477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 145276133969419576567655651 217914200954129364851483477)
                    ·
                      refine ⟨1276841021215601747176661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 217914200954129364851483477 1276841021215601747176661)
                      ·
                        rfl

theorem cell23_2486639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_2486639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486639 prefixEnd_2486639 := by exact prefixLift 2486639
  have htrace : WordTrace (prefixWord ++ tailWord_2486639) baseStart_2486639 baseEnd_2486639 := by
    simpa [prefixWord, tailWord_2486639, baseEnd_2486639] using wordTrace_append hprefix tailTrace_2486639
  have hstable : (prefixWord ++ tailWord_2486639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486639).length < 2 ^ (prefixWord ++ tailWord_2486639).sum := by decide
  have hdescent : baseEnd_2486639 < baseStart_2486639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486640 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 4, 2, 2]
def baseStart_2486640 : Nat := 118140960795 + 2486640 * 2 ^ 59
def prefixEnd_2486640 : Nat := 4983230072969 + 3 ^ 40 * 2486640 * 2
def baseEnd_2486640 : Nat := 1276841534696256243264157

theorem tailTrace_2486640 : CollatzResearch.WordTrace tailWord_2486640 prefixEnd_2486640 1276841534696256243264157 := by
  unfold tailWord_2486640
  simp only [CollatzResearch.WordTrace]
  refine ⟨45347605855667719573132687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60463474474223626097510249 45347605855667719573132687)
  ·
    refine ⟨68021408783501579359699031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45347605855667719573132687 68021408783501579359699031)
    ·
      refine ⟨102032113175252369039548547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68021408783501579359699031 102032113175252369039548547)
      ·
        refine ⟨153048169762878553559322821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102032113175252369039548547 153048169762878553559322821)
        ·
          refine ⟨28696531830539728792373029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153048169762878553559322821 28696531830539728792373029)
          ·
            refine ⟨5380599718226199148569943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28696531830539728792373029 5380599718226199148569943)
            ·
              refine ⟨8070899577339298722854915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5380599718226199148569943 8070899577339298722854915)
              ·
                refine ⟨12106349366008948084282373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8070899577339298722854915 12106349366008948084282373)
                ·
                  refine ⟨2269940506126677765802945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12106349366008948084282373 2269940506126677765802945)
                  ·
                    refine ⟨1702455379595008324352209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2269940506126677765802945 1702455379595008324352209)
                    ·
                      refine ⟨1276841534696256243264157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1702455379595008324352209 1276841534696256243264157)
                      ·
                        rfl

theorem cell23_2486640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 4, 2, 2].length) (baseStart_2486640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486640 prefixEnd_2486640 := by exact prefixLift 2486640
  have htrace : WordTrace (prefixWord ++ tailWord_2486640) baseStart_2486640 baseEnd_2486640 := by
    simpa [prefixWord, tailWord_2486640, baseEnd_2486640] using wordTrace_append hprefix tailTrace_2486640
  have hstable : (prefixWord ++ tailWord_2486640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486640).length < 2 ^ (prefixWord ++ tailWord_2486640).sum := by decide
  have hdescent : baseEnd_2486640 < baseStart_2486640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486657 : List Nat := [1, 2, 4, 3, 1, 3, 1, 1, 1, 4, 2]
def baseStart_2486657 : Nat := 118140960795 + 2486657 * 2 ^ 59
def prefixEnd_2486657 : Nat := 4983230072969 + 3 ^ 40 * 2486657 * 2
def baseEnd_2486657 : Nat := 1276850263867382676751579

theorem tailTrace_2486657 : CollatzResearch.WordTrace tailWord_2486657 prefixEnd_2486657 1276850263867382676751579 := by
  unfold tailWord_2486657
  simp only [CollatzResearch.WordTrace]
  refine ⟨90695831752273851049634225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60463887834849234033089483 90695831752273851049634225)
  ·
    refine ⟨68021873814205388287225669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90695831752273851049634225 68021873814205388287225669)
    ·
      refine ⟨12754101340163510303854813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68021873814205388287225669 12754101340163510303854813)
      ·
        refine ⟨4782788002561316363945555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12754101340163510303854813 4782788002561316363945555)
        ·
          refine ⟨7174182003841974545918333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4782788002561316363945555 7174182003841974545918333)
          ·
            refine ⟨2690318251440740454719375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7174182003841974545918333 2690318251440740454719375)
            ·
              refine ⟨4035477377161110682079063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2690318251440740454719375 4035477377161110682079063)
              ·
                refine ⟨6053216065741666023118595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4035477377161110682079063 6053216065741666023118595)
                ·
                  refine ⟨9079824098612499034677893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6053216065741666023118595 9079824098612499034677893)
                  ·
                    refine ⟨1702467018489843569002105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9079824098612499034677893 1702467018489843569002105)
                    ·
                      refine ⟨1276850263867382676751579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1702467018489843569002105 1276850263867382676751579)
                      ·
                        rfl

theorem cell23_2486657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_2486657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486657 prefixEnd_2486657 := by exact prefixLift 2486657
  have htrace : WordTrace (prefixWord ++ tailWord_2486657) baseStart_2486657 baseEnd_2486657 := by
    simpa [prefixWord, tailWord_2486657, baseEnd_2486657] using wordTrace_append hprefix tailTrace_2486657
  have hstable : (prefixWord ++ tailWord_2486657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486657).length < 2 ^ (prefixWord ++ tailWord_2486657).sum := by decide
  have hdescent : baseEnd_2486657 < baseStart_2486657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486680 : List Nat := [2, 1, 2, 5, 1, 1, 3, 3, 5]
def baseStart_2486680 : Nat := 118140960795 + 2486680 * 2 ^ 59
def prefixEnd_2486680 : Nat := 4983230072969 + 3 ^ 40 * 2486680 * 2
def baseEnd_2486680 : Nat := 141873563769159565195997

theorem tailTrace_2486680 : CollatzResearch.WordTrace tailWord_2486680 prefixEnd_2486680 141873563769159565195997 := by
  unfold tailWord_2486680
  simp only [CollatzResearch.WordTrace]
  refine ⟨45348335315595262988860747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60464447087460350651814329 45348335315595262988860747)
  ·
    refine ⟨68022502973392894483291121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45348335315595262988860747 68022502973392894483291121)
    ·
      refine ⟨51016877230044670862468341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68022502973392894483291121 51016877230044670862468341)
      ·
        refine ⟨4782832240316687893356407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51016877230044670862468341 4782832240316687893356407)
        ·
          refine ⟨7174248360475031840034611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4782832240316687893356407 7174248360475031840034611)
          ·
            refine ⟨10761372540712547760051917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7174248360475031840034611 10761372540712547760051917)
            ·
              refine ⟨4035514702767205410019469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10761372540712547760051917 4035514702767205410019469)
              ·
                refine ⟨1513318013537702028757301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4035514702767205410019469 1513318013537702028757301)
                ·
                  refine ⟨141873563769159565195997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1513318013537702028757301 141873563769159565195997)
                  ·
                    rfl

theorem cell23_2486680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 3, 5].length) (baseStart_2486680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486680 prefixEnd_2486680 := by exact prefixLift 2486680
  have htrace : WordTrace (prefixWord ++ tailWord_2486680) baseStart_2486680 baseEnd_2486680 := by
    simpa [prefixWord, tailWord_2486680, baseEnd_2486680] using wordTrace_append hprefix tailTrace_2486680
  have hstable : (prefixWord ++ tailWord_2486680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486680).length < 2 ^ (prefixWord ++ tailWord_2486680).sum := by decide
  have hdescent : baseEnd_2486680 < baseStart_2486680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486753 : List Nat := [1, 2, 3, 1, 2, 2, 4, 2, 6]
def baseStart_2486753 : Nat := 118140960795 + 2486753 * 2 ^ 59
def prefixEnd_2486753 : Nat := 4983230072969 + 3 ^ 40 * 2486753 * 2
def baseEnd_2486753 : Nat := 141877728667801589016793

theorem tailTrace_2486753 : CollatzResearch.WordTrace tailWord_2486753 prefixEnd_2486753 141877728667801589016793 := by
  unfold tailWord_2486753
  simp only [CollatzResearch.WordTrace]
  refine ⟨90699333159926059445128913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60466222106617372963419275 90699333159926059445128913)
  ·
    refine ⟨68024499869944544583846685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90699333159926059445128913 68024499869944544583846685)
    ·
      refine ⟨25509187451229204218942507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68024499869944544583846685 25509187451229204218942507)
      ·
        refine ⟨38263781176843806328413761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25509187451229204218942507 38263781176843806328413761)
        ·
          refine ⟨28697835882632854746310321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38263781176843806328413761 28697835882632854746310321)
          ·
            refine ⟨21523376911974641059732741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28697835882632854746310321 21523376911974641059732741)
            ·
              refine ⟨4035633170995245198699889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21523376911974641059732741 4035633170995245198699889)
              ·
                refine ⟨3026724878246433899024917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4035633170995245198699889 3026724878246433899024917)
                ·
                  refine ⟨141877728667801589016793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3026724878246433899024917 141877728667801589016793)
                  ·
                    rfl

theorem cell23_2486753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 6].length) (baseStart_2486753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486753 prefixEnd_2486753 := by exact prefixLift 2486753
  have htrace : WordTrace (prefixWord ++ tailWord_2486753) baseStart_2486753 baseEnd_2486753 := by
    simpa [prefixWord, tailWord_2486753, baseEnd_2486753] using wordTrace_append hprefix tailTrace_2486753
  have hstable : (prefixWord ++ tailWord_2486753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486753).length < 2 ^ (prefixWord ++ tailWord_2486753).sum := by decide
  have hdescent : baseEnd_2486753 < baseStart_2486753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486776 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 7]
def baseStart_2486776 : Nat := 118140960795 + 2486776 * 2 ^ 59
def prefixEnd_2486776 : Nat := 4983230072969 + 3 ^ 40 * 2486776 * 2
def baseEnd_2486776 : Nat := 1276911368065267711163531

theorem tailTrace_2486776 : CollatzResearch.WordTrace tailWord_2486776 prefixEnd_2486776 1276911368065267711163531 := by
  unfold tailWord_2486776
  simp only [CollatzResearch.WordTrace]
  refine ⟨45350086019421367186608091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60466781359228489582144121 45350086019421367186608091)
  ·
    refine ⟨68025129029132050779912137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45350086019421367186608091 68025129029132050779912137)
    ·
      refine ⟨51018846771849038084934103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68025129029132050779912137 51018846771849038084934103)
      ·
        refine ⟨76528270157773557127401155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51018846771849038084934103 76528270157773557127401155)
        ·
          refine ⟨114792405236660335691101733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76528270157773557127401155 114792405236660335691101733)
          ·
            refine ⟨21523575981873812942081575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114792405236660335691101733 21523575981873812942081575)
            ·
              refine ⟨32285363972810719413122363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21523575981873812942081575 32285363972810719413122363)
              ·
                refine ⟨48428045959216079119683545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32285363972810719413122363 48428045959216079119683545)
                ·
                  refine ⟨36321034469412059339762659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48428045959216079119683545 36321034469412059339762659)
                  ·
                    refine ⟨54481551704118089009643989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36321034469412059339762659 54481551704118089009643989)
                    ·
                      refine ⟨1276911368065267711163531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54481551704118089009643989 1276911368065267711163531)
                      ·
                        rfl

theorem cell23_2486776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_2486776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486776 prefixEnd_2486776 := by exact prefixLift 2486776
  have htrace : WordTrace (prefixWord ++ tailWord_2486776) baseStart_2486776 baseEnd_2486776 := by
    simpa [prefixWord, tailWord_2486776, baseEnd_2486776] using wordTrace_append hprefix tailTrace_2486776
  have hstable : (prefixWord ++ tailWord_2486776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486776).length < 2 ^ (prefixWord ++ tailWord_2486776).sum := by decide
  have hdescent : baseEnd_2486776 < baseStart_2486776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486783 : List Nat := [1, 1, 2, 2, 1, 2, 4, 4, 1, 5]
def baseStart_2486783 : Nat := 118140960795 + 2486783 * 2 ^ 59
def prefixEnd_2486783 : Nat := 4983230072969 + 3 ^ 40 * 2486783 * 2
def baseEnd_2486783 : Nat := 425638320809949727925333

theorem tailTrace_2486783 : CollatzResearch.WordTrace tailWord_2486783 prefixEnd_2486783 425638320809949727925333 := by
  unfold tailWord_2486783
  simp only [CollatzResearch.WordTrace]
  refine ⟨90700427349817374568721003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60466951566544916379147335 90700427349817374568721003)
  ·
    refine ⟨136050641024726061853081505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90700427349817374568721003 136050641024726061853081505)
    ·
      refine ⟨102037980768544546389811129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136050641024726061853081505 102037980768544546389811129)
      ·
        refine ⟨76528485576408409792358347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102037980768544546389811129 76528485576408409792358347)
        ·
          refine ⟨114792728364612614688537521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76528485576408409792358347 114792728364612614688537521)
          ·
            refine ⟨86094546273459461016403141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114792728364612614688537521 86094546273459461016403141)
            ·
              refine ⟨16142727426273648940575589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86094546273459461016403141 16142727426273648940575589)
              ·
                refine ⟨3026761392426309176357923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16142727426273648940575589 3026761392426309176357923)
                ·
                  refine ⟨4540142088639463764536885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3026761392426309176357923 4540142088639463764536885)
                  ·
                    refine ⟨425638320809949727925333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4540142088639463764536885 425638320809949727925333)
                    ·
                      rfl

theorem cell23_2486783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 1, 5].length) (baseStart_2486783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486783 prefixEnd_2486783 := by exact prefixLift 2486783
  have htrace : WordTrace (prefixWord ++ tailWord_2486783) baseStart_2486783 baseEnd_2486783 := by
    simpa [prefixWord, tailWord_2486783, baseEnd_2486783] using wordTrace_append hprefix tailTrace_2486783
  have hstable : (prefixWord ++ tailWord_2486783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486783).length < 2 ^ (prefixWord ++ tailWord_2486783).sum := by decide
  have hdescent : baseEnd_2486783 < baseStart_2486783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486837 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 3, 2, 2]
def baseStart_2486837 : Nat := 118140960795 + 2486837 * 2 ^ 59
def prefixEnd_2486837 : Nat := 4983230072969 + 3 ^ 40 * 2486837 * 2
def baseEnd_2486837 : Nat := 1276942690385191972500751

theorem tailTrace_2486837 : CollatzResearch.WordTrace tailWord_2486837 prefixEnd_2486837 1276942690385191972500751 := by
  unfold tailWord_2486837
  simp only [CollatzResearch.WordTrace]
  refine ⟨90702396891621741791186765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60468264594414494527457843 90702396891621741791186765)
  ·
    refine ⟨34013398834358153171695037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90702396891621741791186765 34013398834358153171695037)
    ·
      refine ⟨12755024562884307439385639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34013398834358153171695037 12755024562884307439385639)
      ·
        refine ⟨19132536844326461159078459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12755024562884307439385639 19132536844326461159078459)
        ·
          refine ⟨28698805266489691738617689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19132536844326461159078459 28698805266489691738617689)
          ·
            refine ⟨21524103949867268803963267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28698805266489691738617689 21524103949867268803963267)
            ·
              refine ⟨32286155924800903205944901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21524103949867268803963267 32286155924800903205944901)
              ·
                refine ⟨6053654235900169351114669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32286155924800903205944901 6053654235900169351114669)
                ·
                  refine ⟨2270120338462563506668001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6053654235900169351114669 2270120338462563506668001)
                  ·
                    refine ⟨1702590253846922630001001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2270120338462563506668001 1702590253846922630001001)
                    ·
                      refine ⟨1276942690385191972500751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1702590253846922630001001 1276942690385191972500751)
                      ·
                        rfl

theorem cell23_2486837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_2486837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486837 prefixEnd_2486837 := by exact prefixLift 2486837
  have htrace : WordTrace (prefixWord ++ tailWord_2486837) baseStart_2486837 baseEnd_2486837 := by
    simpa [prefixWord, tailWord_2486837, baseEnd_2486837] using wordTrace_append hprefix tailTrace_2486837
  have hstable : (prefixWord ++ tailWord_2486837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486837).length < 2 ^ (prefixWord ++ tailWord_2486837).sum := by decide
  have hdescent : baseEnd_2486837 < baseStart_2486837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486854 : List Nat := [6, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_2486854 : Nat := 118140960795 + 2486854 * 2 ^ 59
def prefixEnd_2486854 : Nat := 4983230072969 + 3 ^ 40 * 2486854 * 2
def baseEnd_2486854 : Nat := 1276951419556318405988173

theorem tailTrace_2486854 : CollatzResearch.WordTrace tailWord_2486854 prefixEnd_2486854 1276951419556318405988173 := by
  unfold tailWord_2486854
  simp only [CollatzResearch.WordTrace]
  refine ⟨2834469279142504802954863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60468677955040102463037077 2834469279142504802954863)
  ·
    refine ⟨4251703918713757204432295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2834469279142504802954863 4251703918713757204432295)
    ·
      refine ⟨6377555878070635806648443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4251703918713757204432295 6377555878070635806648443)
      ·
        refine ⟨9566333817105953709972665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6377555878070635806648443 9566333817105953709972665)
        ·
          refine ⟨7174750362829465282479499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9566333817105953709972665 7174750362829465282479499)
          ·
            refine ⟨10762125544244197923719249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7174750362829465282479499 10762125544244197923719249)
            ·
              refine ⟨8071594158183148442789437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10762125544244197923719249 8071594158183148442789437)
              ·
                refine ⟨3026847809318680666046039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8071594158183148442789437 3026847809318680666046039)
                ·
                  refine ⟨4540271713978020999069059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3026847809318680666046039 4540271713978020999069059)
                  ·
                    refine ⟨6810407570967031498603589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4540271713978020999069059 6810407570967031498603589)
                    ·
                      refine ⟨1276951419556318405988173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6810407570967031498603589 1276951419556318405988173)
                      ·
                        rfl

theorem cell23_2486854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_2486854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486854 prefixEnd_2486854 := by exact prefixLift 2486854
  have htrace : WordTrace (prefixWord ++ tailWord_2486854) baseStart_2486854 baseEnd_2486854 := by
    simpa [prefixWord, tailWord_2486854, baseEnd_2486854] using wordTrace_append hprefix tailTrace_2486854
  have hstable : (prefixWord ++ tailWord_2486854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486854).length < 2 ^ (prefixWord ++ tailWord_2486854).sum := by decide
  have hdescent : baseEnd_2486854 < baseStart_2486854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486871 : List Nat := [1, 1, 3, 2, 2, 2, 5, 2, 1, 2, 2]
def baseStart_2486871 : Nat := 118140960795 + 2486871 * 2 ^ 59
def prefixEnd_2486871 : Nat := 4983230072969 + 3 ^ 40 * 2486871 * 2
def baseEnd_2486871 : Nat := 1276960148727444839475595

theorem tailTrace_2486871 : CollatzResearch.WordTrace tailWord_2486871 prefixEnd_2486871 1276960148727444839475595 := by
  unfold tailWord_2486871
  simp only [CollatzResearch.WordTrace]
  refine ⟨90703636973498565597924467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60469091315665710398616311 90703636973498565597924467)
  ·
    refine ⟨136055455460247848396886701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90703636973498565597924467 136055455460247848396886701)
    ·
      refine ⟨51020795797592943148832513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136055455460247848396886701 51020795797592943148832513)
      ·
        refine ⟨38265596848194707361624385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51020795797592943148832513 38265596848194707361624385)
        ·
          refine ⟨28699197636146030521218289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38265596848194707361624385 28699197636146030521218289)
          ·
            refine ⟨21524398227109522890913717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28699197636146030521218289 21524398227109522890913717)
            ·
              refine ⟨2017912333791517771023161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21524398227109522890913717 2017912333791517771023161)
              ·
                refine ⟨1513434250343638328267371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2017912333791517771023161 1513434250343638328267371)
                ·
                  refine ⟨2270151375515457492401057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1513434250343638328267371 2270151375515457492401057)
                  ·
                    refine ⟨1702613531636593119300793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2270151375515457492401057 1702613531636593119300793)
                    ·
                      refine ⟨1276960148727444839475595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1702613531636593119300793 1276960148727444839475595)
                      ·
                        rfl

theorem cell23_2486871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_2486871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486871 prefixEnd_2486871 := by exact prefixLift 2486871
  have htrace : WordTrace (prefixWord ++ tailWord_2486871) baseStart_2486871 baseEnd_2486871 := by
    simpa [prefixWord, tailWord_2486871, baseEnd_2486871] using wordTrace_append hprefix tailTrace_2486871
  have hstable : (prefixWord ++ tailWord_2486871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486871).length < 2 ^ (prefixWord ++ tailWord_2486871).sum := by decide
  have hdescent : baseEnd_2486871 < baseStart_2486871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486940 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_2486940 : Nat := 118140960795 + 2486940 * 2 ^ 59
def prefixEnd_2486940 : Nat := 4983230072969 + 3 ^ 40 * 2486940 * 2
def baseEnd_2486940 : Nat := 1276995578892605069512777

theorem tailTrace_2486940 : CollatzResearch.WordTrace tailWord_2486940 prefixEnd_2486940 1276995578892605069512777 := by
  unfold tailWord_2486940
  simp only [CollatzResearch.WordTrace]
  refine ⟨45353076805124295191093137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60470769073499060254790849 45353076805124295191093137)
  ·
    refine ⟨34014807603843221393319853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45353076805124295191093137 34014807603843221393319853)
    ·
      refine ⟨12755552851441208022494945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34014807603843221393319853 12755552851441208022494945)
      ·
        refine ⟨9566664638580906016871209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12755552851441208022494945 9566664638580906016871209)
        ·
          refine ⟨7174998478935679512653407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9566664638580906016871209 7174998478935679512653407)
          ·
            refine ⟨10762497718403519268980111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7174998478935679512653407 10762497718403519268980111)
            ·
              refine ⟨16143746577605278903470167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10762497718403519268980111 16143746577605278903470167)
              ·
                refine ⟨24215619866407918355205251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16143746577605278903470167 24215619866407918355205251)
                ·
                  refine ⟨36323429799611877532807877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24215619866407918355205251 36323429799611877532807877)
                  ·
                    refine ⟨6810643087427227037401477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36323429799611877532807877 6810643087427227037401477)
                    ·
                      refine ⟨1276995578892605069512777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6810643087427227037401477 1276995578892605069512777)
                      ·
                        rfl

theorem cell23_2486940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_2486940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486940 prefixEnd_2486940 := by exact prefixLift 2486940
  have htrace : WordTrace (prefixWord ++ tailWord_2486940) baseStart_2486940 baseEnd_2486940 := by
    simpa [prefixWord, tailWord_2486940, baseEnd_2486940] using wordTrace_append hprefix tailTrace_2486940
  have hstable : (prefixWord ++ tailWord_2486940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486940).length < 2 ^ (prefixWord ++ tailWord_2486940).sum := by decide
  have hdescent : baseEnd_2486940 < baseStart_2486940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2486944 : List Nat := [2, 1, 1, 4, 4, 1, 2, 1, 1, 4, 2]
def baseStart_2486944 : Nat := 118140960795 + 2486944 * 2 ^ 59
def prefixEnd_2486944 : Nat := 4983230072969 + 3 ^ 40 * 2486944 * 2
def baseEnd_2486944 : Nat := 1276997632815223053862759

theorem tailTrace_2486944 : CollatzResearch.WordTrace tailWord_2486944 prefixEnd_2486944 1276997632815223053862759 := by
  unfold tailWord_2486944
  simp only [CollatzResearch.WordTrace]
  refine ⟨45353149751117049532665943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60470866334822732710221257 45353149751117049532665943)
  ·
    refine ⟨68029724626675574298998915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45353149751117049532665943 68029724626675574298998915)
    ·
      refine ⟨102044586940013361448498373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68029724626675574298998915 102044586940013361448498373)
      ·
        refine ⟨19133360051252505271593445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102044586940013361448498373 19133360051252505271593445)
        ·
          refine ⟨3587505009609844738423771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19133360051252505271593445 3587505009609844738423771)
          ·
            refine ⟨5381257514414767107635657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3587505009609844738423771 5381257514414767107635657)
            ·
              refine ⟨4035943135811075330726743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5381257514414767107635657 4035943135811075330726743)
              ·
                refine ⟨6053914703716612996090115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4035943135811075330726743 6053914703716612996090115)
                ·
                  refine ⟨9080872055574919494135173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6053914703716612996090115 9080872055574919494135173)
                  ·
                    refine ⟨1702663510420297405150345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9080872055574919494135173 1702663510420297405150345)
                    ·
                      refine ⟨1276997632815223053862759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1702663510420297405150345 1276997632815223053862759)
                      ·
                        rfl

theorem cell23_2486944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_2486944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2486944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2486944 prefixEnd_2486944 := by exact prefixLift 2486944
  have htrace : WordTrace (prefixWord ++ tailWord_2486944) baseStart_2486944 baseEnd_2486944 := by
    simpa [prefixWord, tailWord_2486944, baseEnd_2486944] using wordTrace_append hprefix tailTrace_2486944
  have hstable : (prefixWord ++ tailWord_2486944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2486944).length < 2 ^ (prefixWord ++ tailWord_2486944).sum := by decide
  have hdescent : baseEnd_2486944 < baseStart_2486944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2486944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487000 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 1, 3, 4]
def baseStart_2487000 : Nat := 118140960795 + 2487000 * 2 ^ 59
def prefixEnd_2487000 : Nat := 4983230072969 + 3 ^ 40 * 2487000 * 2
def baseEnd_2487000 : Nat := 1277026387731874834762501

theorem tailTrace_2487000 : CollatzResearch.WordTrace tailWord_2487000 prefixEnd_2487000 1277026387731874834762501 := by
  unfold tailWord_2487000
  simp only [CollatzResearch.WordTrace]
  refine ⟨45354170995015610314685227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60472227993354147086246969 45354170995015610314685227)
  ·
    refine ⟨68031256492523415472027841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45354170995015610314685227 68031256492523415472027841)
    ·
      refine ⟨51023442369392561604020881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68031256492523415472027841 51023442369392561604020881)
      ·
        refine ⟨38267581777044421203015661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51023442369392561604020881 38267581777044421203015661)
        ·
          refine ⟨14350343166391657951130873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38267581777044421203015661 14350343166391657951130873)
          ·
            refine ⟨10762757374793743463348155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14350343166391657951130873 10762757374793743463348155)
            ·
              refine ⟨16144136062190615195022233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10762757374793743463348155 16144136062190615195022233)
              ·
                refine ⟨12108102046642961396266675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16144136062190615195022233 12108102046642961396266675)
                ·
                  refine ⟨18162153069964442094400013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12108102046642961396266675 18162153069964442094400013)
                  ·
                    refine ⟨6810807401236665785400005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18162153069964442094400013 6810807401236665785400005)
                    ·
                      refine ⟨1277026387731874834762501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6810807401236665785400005 1277026387731874834762501)
                      ·
                        rfl

theorem cell23_2487000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_2487000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487000 prefixEnd_2487000 := by exact prefixLift 2487000
  have htrace : WordTrace (prefixWord ++ tailWord_2487000) baseStart_2487000 baseEnd_2487000 := by
    simpa [prefixWord, tailWord_2487000, baseEnd_2487000] using wordTrace_append hprefix tailTrace_2487000
  have hstable : (prefixWord ++ tailWord_2487000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487000).length < 2 ^ (prefixWord ++ tailWord_2487000).sum := by decide
  have hdescent : baseEnd_2487000 < baseStart_2487000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487003 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 5]
def baseStart_2487003 : Nat := 118140960795 + 2487003 * 2 ^ 59
def prefixEnd_2487003 : Nat := 4983230072969 + 3 ^ 40 * 2487003 * 2
def baseEnd_2487003 : Nat := 1277027928173838323024987

theorem tailTrace_2487003 : CollatzResearch.WordTrace tailWord_2487003 prefixEnd_2487003 1277027928173838323024987 := by
  unfold tailWord_2487003
  simp only [CollatzResearch.WordTrace]
  refine ⟨90708451409020352141729663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60472300939346901427819775 90708451409020352141729663)
  ·
    refine ⟨136062677113530528212594495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90708451409020352141729663 136062677113530528212594495)
    ·
      refine ⟨204094015670295792318891743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136062677113530528212594495 204094015670295792318891743)
      ·
        refine ⟨306141023505443688478337615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204094015670295792318891743 306141023505443688478337615)
        ·
          refine ⟨459211535258165532717506423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306141023505443688478337615 459211535258165532717506423)
          ·
            refine ⟨688817302887248299076259635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459211535258165532717506423 688817302887248299076259635)
            ·
              refine ⟨1033225954330872448614389453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688817302887248299076259635 1033225954330872448614389453)
              ·
                refine ⟨387459732874077168230396045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1033225954330872448614389453 387459732874077168230396045)
                ·
                  refine ⟨145297399827778938086398517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387459732874077168230396045 145297399827778938086398517)
                  ·
                    refine ⟨13621631233854275445599861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 145297399827778938086398517 13621631233854275445599861)
                    ·
                      refine ⟨1277027928173838323024987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13621631233854275445599861 1277027928173838323024987)
                      ·
                        rfl

theorem cell23_2487003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 5].length) (baseStart_2487003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487003 prefixEnd_2487003 := by exact prefixLift 2487003
  have htrace : WordTrace (prefixWord ++ tailWord_2487003) baseStart_2487003 baseEnd_2487003 := by
    simpa [prefixWord, tailWord_2487003, baseEnd_2487003] using wordTrace_append hprefix tailTrace_2487003
  have hstable : (prefixWord ++ tailWord_2487003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487003).length < 2 ^ (prefixWord ++ tailWord_2487003).sum := by decide
  have hdescent : baseEnd_2487003 < baseStart_2487003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487037 : List Nat := [1, 4, 1, 1, 1, 1, 5, 2, 2, 2, 3]
def baseStart_2487037 : Nat := 118140960795 + 2487037 * 2 ^ 59
def prefixEnd_2487037 : Nat := 4983230072969 + 3 ^ 40 * 2487037 * 2
def baseEnd_2487037 : Nat := 1277045386516091189999831

theorem tailTrace_2487037 : CollatzResearch.WordTrace tailWord_2487037 prefixEnd_2487037 1277045386516091189999831 := by
  unfold tailWord_2487037
  simp only [CollatzResearch.WordTrace]
  refine ⟨90709691490897175948467365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60473127660598117298978243 90709691490897175948467365)
  ·
    refine ⟨17008067154543220490337631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90709691490897175948467365 17008067154543220490337631)
    ·
      refine ⟨25512100731814830735506447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17008067154543220490337631 25512100731814830735506447)
      ·
        refine ⟨38268151097722246103259671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25512100731814830735506447 38268151097722246103259671)
        ·
          refine ⟨57402226646583369154889507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38268151097722246103259671 57402226646583369154889507)
          ·
            refine ⟨86103339969875053732334261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57402226646583369154889507 86103339969875053732334261)
            ·
              refine ⟨8072188122175786287406337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86103339969875053732334261 8072188122175786287406337)
              ·
                refine ⟨6054141091631839715554753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8072188122175786287406337 6054141091631839715554753)
                ·
                  refine ⟨4540605818723879786666065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6054141091631839715554753 4540605818723879786666065)
                  ·
                    refine ⟨3405454364042909839999549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4540605818723879786666065 3405454364042909839999549)
                    ·
                      refine ⟨1277045386516091189999831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3405454364042909839999549 1277045386516091189999831)
                      ·
                        rfl

theorem cell23_2487037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_2487037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487037 prefixEnd_2487037 := by exact prefixLift 2487037
  have htrace : WordTrace (prefixWord ++ tailWord_2487037) baseStart_2487037 baseEnd_2487037 := by
    simpa [prefixWord, tailWord_2487037, baseEnd_2487037] using wordTrace_append hprefix tailTrace_2487037
  have hstable : (prefixWord ++ tailWord_2487037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487037).length < 2 ^ (prefixWord ++ tailWord_2487037).sum := by decide
  have hdescent : baseEnd_2487037 < baseStart_2487037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487057 : List Nat := [1, 2, 2, 1, 1, 3, 6, 1, 6]
def baseStart_2487057 : Nat := 118140960795 + 2487057 * 2 ^ 59
def prefixEnd_2487057 : Nat := 4983230072969 + 3 ^ 40 * 2487057 * 2
def baseEnd_2487057 : Nat := 141895072903242345749971

theorem tailTrace_2487057 : CollatzResearch.WordTrace tailWord_2487057 prefixEnd_2487057 141895072903242345749971 := by
  unfold tailWord_2487057
  simp only [CollatzResearch.WordTrace]
  refine ⟨90710420950824719364195425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60473613967216479576130283 90710420950824719364195425)
  ·
    refine ⟨68032815713118539523146569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90710420950824719364195425 68032815713118539523146569)
    ·
      refine ⟨51024611784838904642359927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68032815713118539523146569 51024611784838904642359927)
      ·
        refine ⟨76536917677258356963539891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51024611784838904642359927 76536917677258356963539891)
        ·
          refine ⟨114805376515887535445309837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76536917677258356963539891 114805376515887535445309837)
          ·
            refine ⟨43052016193457825791991189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114805376515887535445309837 43052016193457825791991189)
            ·
              refine ⟨2018063259068335583999587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43052016193457825791991189 2018063259068335583999587)
              ·
                refine ⟨3027094888602503375999381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018063259068335583999587 3027094888602503375999381)
                ·
                  refine ⟨141895072903242345749971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3027094888602503375999381 141895072903242345749971)
                  ·
                    rfl

theorem cell23_2487057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 6, 1, 6].length) (baseStart_2487057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487057 prefixEnd_2487057 := by exact prefixLift 2487057
  have htrace : WordTrace (prefixWord ++ tailWord_2487057) baseStart_2487057 baseEnd_2487057 := by
    simpa [prefixWord, tailWord_2487057, baseEnd_2487057] using wordTrace_append hprefix tailTrace_2487057
  have hstable : (prefixWord ++ tailWord_2487057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487057).length < 2 ^ (prefixWord ++ tailWord_2487057).sum := by decide
  have hdescent : baseEnd_2487057 < baseStart_2487057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487100 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 5, 6]
def baseStart_2487100 : Nat := 118140960795 + 2487100 * 2 ^ 59
def prefixEnd_2487100 : Nat := 4983230072969 + 3 ^ 40 * 2487100 * 2
def baseEnd_2487100 : Nat := 425692578599108147837347

theorem tailTrace_2487100 : CollatzResearch.WordTrace tailWord_2487100 prefixEnd_2487100 425692578599108147837347 := by
  unfold tailWord_2487100
  simp only [CollatzResearch.WordTrace]
  refine ⟨45355994644834468854005377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60474659526445958472007169 45355994644834468854005377)
  ·
    refine ⟨34016995983625851640504033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45355994644834468854005377 34016995983625851640504033)
    ·
      refine ⟨25512746987719388730378025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34016995983625851640504033 25512746987719388730378025)
      ·
        refine ⟨19134560240789541547783519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25512746987719388730378025 19134560240789541547783519)
        ·
          refine ⟨28701840361184312321675279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19134560240789541547783519 28701840361184312321675279)
          ·
            refine ⟨43052760541776468482512919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28701840361184312321675279 43052760541776468482512919)
            ·
              refine ⟨64579140812664702723769379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43052760541776468482512919 64579140812664702723769379)
              ·
                refine ⟨96868711218997054085654069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64579140812664702723769379 96868711218997054085654069)
                ·
                  refine ⟨9081441676780973820530069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96868711218997054085654069 9081441676780973820530069)
                  ·
                    refine ⟨425692578599108147837347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9081441676780973820530069 425692578599108147837347)
                    ·
                      rfl

theorem cell23_2487100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_2487100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487100 prefixEnd_2487100 := by exact prefixLift 2487100
  have htrace : WordTrace (prefixWord ++ tailWord_2487100) baseStart_2487100 baseEnd_2487100 := by
    simpa [prefixWord, tailWord_2487100, baseEnd_2487100] using wordTrace_append hprefix tailTrace_2487100
  have hstable : (prefixWord ++ tailWord_2487100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487100).length < 2 ^ (prefixWord ++ tailWord_2487100).sum := by decide
  have hdescent : baseEnd_2487100 < baseStart_2487100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487120 : List Nat := [2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 6]
def baseStart_2487120 : Nat := 118140960795 + 2487120 * 2 ^ 59
def prefixEnd_2487120 : Nat := 4983230072969 + 3 ^ 40 * 2487120 * 2
def baseEnd_2487120 : Nat := 1277088005410414365261949

theorem tailTrace_2487120 : CollatzResearch.WordTrace tailWord_2487120 prefixEnd_2487120 1277088005410414365261949 := by
  unfold tailWord_2487120
  simp only [CollatzResearch.WordTrace]
  refine ⟨45356359374798240561869407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60475145833064320749159209 45356359374798240561869407)
  ·
    refine ⟨68034539062197360842804111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45356359374798240561869407 68034539062197360842804111)
    ·
      refine ⟨102051808593296041264206167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68034539062197360842804111 102051808593296041264206167)
      ·
        refine ⟨153077712889944061896309251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102051808593296041264206167 153077712889944061896309251)
        ·
          refine ⟨229616569334916092844463877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153077712889944061896309251 229616569334916092844463877)
          ·
            refine ⟨43053106750296767408336977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 229616569334916092844463877 43053106750296767408336977)
            ·
              refine ⟨32289830062722575556252733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43053106750296767408336977 32289830062722575556252733)
              ·
                refine ⟨12108686273520965833594775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32289830062722575556252733 12108686273520965833594775)
                ·
                  refine ⟨18163029410281448750392163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12108686273520965833594775 18163029410281448750392163)
                  ·
                    refine ⟨27244544115422173125588245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18163029410281448750392163 27244544115422173125588245)
                    ·
                      refine ⟨1277088005410414365261949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27244544115422173125588245 1277088005410414365261949)
                      ·
                        rfl

theorem cell23_2487120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_2487120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487120 prefixEnd_2487120 := by exact prefixLift 2487120
  have htrace : WordTrace (prefixWord ++ tailWord_2487120) baseStart_2487120 baseEnd_2487120 := by
    simpa [prefixWord, tailWord_2487120, baseEnd_2487120] using wordTrace_append hprefix tailTrace_2487120
  have hstable : (prefixWord ++ tailWord_2487120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487120).length < 2 ^ (prefixWord ++ tailWord_2487120).sum := by decide
  have hdescent : baseEnd_2487120 < baseStart_2487120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487138 : List Nat := [3, 3, 2, 1, 3, 2, 2, 1, 1, 5]
def baseStart_2487138 : Nat := 118140960795 + 2487138 * 2 ^ 59
def prefixEnd_2487138 : Nat := 4983230072969 + 3 ^ 40 * 2487138 * 2
def baseEnd_2487138 : Nat := 425699082687398431612289

theorem tailTrace_2487138 : CollatzResearch.WordTrace tailWord_2487138 prefixEnd_2487138 425699082687398431612289 := by
  unfold tailWord_2487138
  simp only [CollatzResearch.WordTrace]
  refine ⟨22678343815882817549473517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60475583509020846798596045 22678343815882817549473517)
  ·
    refine ⟨8504378930956056581052569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22678343815882817549473517 8504378930956056581052569)
    ·
      refine ⟨6378284198217042435789427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8504378930956056581052569 6378284198217042435789427)
      ·
        refine ⟨9567426297325563653684141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6378284198217042435789427 9567426297325563653684141)
        ·
          refine ⟨3587784861497086370131553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9567426297325563653684141 3587784861497086370131553)
          ·
            refine ⟨2690838646122814777598665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3587784861497086370131553 2690838646122814777598665)
            ·
              refine ⟨2018128984592111083198999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2690838646122814777598665 2018128984592111083198999)
              ·
                refine ⟨3027193476888166624798499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018128984592111083198999 3027193476888166624798499)
                ·
                  refine ⟨4540790215332249937197749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3027193476888166624798499 4540790215332249937197749)
                  ·
                    refine ⟨425699082687398431612289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4540790215332249937197749 425699082687398431612289)
                    ·
                      rfl

theorem cell23_2487138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_2487138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487138 prefixEnd_2487138 := by exact prefixLift 2487138
  have htrace : WordTrace (prefixWord ++ tailWord_2487138) baseStart_2487138 baseEnd_2487138 := by
    simpa [prefixWord, tailWord_2487138, baseEnd_2487138] using wordTrace_append hprefix tailTrace_2487138
  have hstable : (prefixWord ++ tailWord_2487138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487138).length < 2 ^ (prefixWord ++ tailWord_2487138).sum := by decide
  have hdescent : baseEnd_2487138 < baseStart_2487138 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487158 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2]
def baseStart_2487158 : Nat := 118140960795 + 2487158 * 2 ^ 59
def prefixEnd_2487158 : Nat := 4983230072969 + 3 ^ 40 * 2487158 * 2
def baseEnd_2487158 : Nat := 1277107517675285216586775

theorem tailTrace_2487158 : CollatzResearch.WordTrace tailWord_2487158 prefixEnd_2487158 1277107517675285216586775 := by
  unfold tailWord_2487158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5669631545216175850851383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60476069815639209075748085 5669631545216175850851383)
  ·
    refine ⟨8504447317824263776277075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5669631545216175850851383 8504447317824263776277075)
    ·
      refine ⟨12756670976736395664415613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8504447317824263776277075 12756670976736395664415613)
      ·
        refine ⟨4783751616276148374155855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12756670976736395664415613 4783751616276148374155855)
        ·
          refine ⟨7175627424414222561233783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4783751616276148374155855 7175627424414222561233783)
          ·
            refine ⟨10763441136621333841850675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7175627424414222561233783 10763441136621333841850675)
            ·
              refine ⟨16145161704932000762776013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10763441136621333841850675 16145161704932000762776013)
              ·
                refine ⟨6054435639349500286041005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16145161704932000762776013 6054435639349500286041005)
                ·
                  refine ⟨2270413364756062607265377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6054435639349500286041005 2270413364756062607265377)
                  ·
                    refine ⟨1702810023567046955449033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2270413364756062607265377 1702810023567046955449033)
                    ·
                      refine ⟨1277107517675285216586775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1702810023567046955449033 1277107517675285216586775)
                      ·
                        rfl

theorem cell23_2487158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_2487158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487158 prefixEnd_2487158 := by exact prefixLift 2487158
  have htrace : WordTrace (prefixWord ++ tailWord_2487158) baseStart_2487158 baseEnd_2487158 := by
    simpa [prefixWord, tailWord_2487158, baseEnd_2487158] using wordTrace_append hprefix tailTrace_2487158
  have hstable : (prefixWord ++ tailWord_2487158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487158).length < 2 ^ (prefixWord ++ tailWord_2487158).sum := by decide
  have hdescent : baseEnd_2487158 < baseStart_2487158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487160 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 2, 7]
def baseStart_2487160 : Nat := 118140960795 + 2487160 * 2 ^ 59
def prefixEnd_2487160 : Nat := 4983230072969 + 3 ^ 40 * 2487160 * 2
def baseEnd_2487160 : Nat := 425702848212198069587255

theorem tailTrace_2487160 : CollatzResearch.WordTrace tailWord_2487160 prefixEnd_2487160 425702848212198069587255 := by
  unfold tailWord_2487160
  simp only [CollatzResearch.WordTrace]
  refine ⟨45357088834725783977597467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60476118446301045303463289 45357088834725783977597467)
  ·
    refine ⟨68035633252088675966396201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45357088834725783977597467 68035633252088675966396201)
    ·
      refine ⟨51026724939066506974797151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68035633252088675966396201 51026724939066506974797151)
      ·
        refine ⟨76540087408599760462195727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51026724939066506974797151 76540087408599760462195727)
        ·
          refine ⟨114810131112899640693293591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76540087408599760462195727 114810131112899640693293591)
          ·
            refine ⟨172215196669349461039940387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114810131112899640693293591 172215196669349461039940387)
            ·
              refine ⟨258322795004024191559910581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172215196669349461039940387 258322795004024191559910581)
              ·
                refine ⟨24217762031627267958741617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 258322795004024191559910581 24217762031627267958741617)
                ·
                  refine ⟨18163321523720450969056213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24217762031627267958741617 18163321523720450969056213)
                  ·
                    refine ⟨425702848212198069587255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18163321523720450969056213 425702848212198069587255)
                    ·
                      rfl

theorem cell23_2487160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_2487160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487160 prefixEnd_2487160 := by exact prefixLift 2487160
  have htrace : WordTrace (prefixWord ++ tailWord_2487160) baseStart_2487160 baseEnd_2487160 := by
    simpa [prefixWord, tailWord_2487160, baseEnd_2487160] using wordTrace_append hprefix tailTrace_2487160
  have hstable : (prefixWord ++ tailWord_2487160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487160).length < 2 ^ (prefixWord ++ tailWord_2487160).sum := by decide
  have hdescent : baseEnd_2487160 < baseStart_2487160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487271 : List Nat := [1, 1, 5, 2, 2, 2, 1, 4, 5]
def baseStart_2487271 : Nat := 118140960795 + 2487271 * 2 ^ 59
def prefixEnd_2487271 : Nat := 4983230072969 + 3 ^ 40 * 2487271 * 2
def baseEnd_2487271 : Nat := 141907282332138141608195

theorem tailTrace_2487271 : CollatzResearch.WordTrace tailWord_2487271 prefixEnd_2487271 141907282332138141608195 := by
  unfold tailWord_2487271
  simp only [CollatzResearch.WordTrace]
  refine ⟨90718226172049433912485667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60478817448032955941657111 90718226172049433912485667)
  ·
    refine ⟨136077339258074150868728501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90718226172049433912485667 136077339258074150868728501)
    ·
      refine ⟨12757250555444451643943297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136077339258074150868728501 12757250555444451643943297)
      ·
        refine ⟨9567937916583338732957473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12757250555444451643943297 9567937916583338732957473)
        ·
          refine ⟨7175953437437504049718105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9567937916583338732957473 7175953437437504049718105)
          ·
            refine ⟨5381965078078128037288579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7175953437437504049718105 5381965078078128037288579)
            ·
              refine ⟨8072947617117192055932869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5381965078078128037288579 8072947617117192055932869)
              ·
                refine ⟨1513677678209473510487413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8072947617117192055932869 1513677678209473510487413)
                ·
                  refine ⟨141907282332138141608195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1513677678209473510487413 141907282332138141608195)
                  ·
                    rfl

theorem cell23_2487271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 4, 5].length) (baseStart_2487271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487271 prefixEnd_2487271 := by exact prefixLift 2487271
  have htrace : WordTrace (prefixWord ++ tailWord_2487271) baseStart_2487271 baseEnd_2487271 := by
    simpa [prefixWord, tailWord_2487271, baseEnd_2487271] using wordTrace_append hprefix tailTrace_2487271
  have hstable : (prefixWord ++ tailWord_2487271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487271).length < 2 ^ (prefixWord ++ tailWord_2487271).sum := by decide
  have hdescent : baseEnd_2487271 < baseStart_2487271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487304 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_2487304 : Nat := 118140960795 + 2487304 * 2 ^ 59
def prefixEnd_2487304 : Nat := 4983230072969 + 3 ^ 40 * 2487304 * 2
def baseEnd_2487304 : Nat := 1277182485850841645361103

theorem tailTrace_2487304 : CollatzResearch.WordTrace tailWord_2487304 prefixEnd_2487304 1277182485850841645361103 := by
  unfold tailWord_2487304
  simp only [CollatzResearch.WordTrace]
  refine ⟨45359714890464940274218483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60479619853953253698957977 45359714890464940274218483)
  ·
    refine ⟨68039572335697410411327725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45359714890464940274218483 68039572335697410411327725)
    ·
      refine ⟨25514839625886528904247897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68039572335697410411327725 25514839625886528904247897)
      ·
        refine ⟨19136129719414896678185923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25514839625886528904247897 19136129719414896678185923)
        ·
          refine ⟨28704194579122345017278885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19136129719414896678185923 28704194579122345017278885)
          ·
            refine ⟨5382036483585439690739791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28704194579122345017278885 5382036483585439690739791)
            ·
              refine ⟨8073054725378159536109687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5382036483585439690739791 8073054725378159536109687)
              ·
                refine ⟨12109582088067239304164531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8073054725378159536109687 12109582088067239304164531)
                ·
                  refine ⟨18164373132100858956246797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12109582088067239304164531 18164373132100858956246797)
                  ·
                    refine ⟨6811639924537822108592549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18164373132100858956246797 6811639924537822108592549)
                    ·
                      refine ⟨1277182485850841645361103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6811639924537822108592549 1277182485850841645361103)
                      ·
                        rfl

theorem cell23_2487304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_2487304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487304 prefixEnd_2487304 := by exact prefixLift 2487304
  have htrace : WordTrace (prefixWord ++ tailWord_2487304) baseStart_2487304 baseEnd_2487304 := by
    simpa [prefixWord, tailWord_2487304, baseEnd_2487304] using wordTrace_append hprefix tailTrace_2487304
  have hstable : (prefixWord ++ tailWord_2487304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487304).length < 2 ^ (prefixWord ++ tailWord_2487304).sum := by decide
  have hdescent : baseEnd_2487304 < baseStart_2487304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487331 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 3, 4]
def baseStart_2487331 : Nat := 118140960795 + 2487331 * 2 ^ 59
def prefixEnd_2487331 : Nat := 4983230072969 + 3 ^ 40 * 2487331 * 2
def baseEnd_2487331 : Nat := 425732116609504346574493

theorem tailTrace_2487331 : CollatzResearch.WordTrace tailWord_2487331 prefixEnd_2487331 425732116609504346574493 := by
  unfold tailWord_2487331
  simp only [CollatzResearch.WordTrace]
  refine ⟨90720414551832064159669847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60480276367888042773113231 90720414551832064159669847)
  ·
    refine ⟨136080621827748096239504771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90720414551832064159669847 136080621827748096239504771)
    ·
      refine ⟨204120932741622144359257157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136080621827748096239504771 204120932741622144359257157)
      ·
        refine ⟨38272674889054152067360717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204120932741622144359257157 38272674889054152067360717)
        ·
          refine ⟨14352253083395307025260269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38272674889054152067360717 14352253083395307025260269)
          ·
            refine ⟨5382094906273240134472601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14352253083395307025260269 5382094906273240134472601)
            ·
              refine ⟨4036571179704930100854451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5382094906273240134472601 4036571179704930100854451)
              ·
                refine ⟨6054856769557395151281677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4036571179704930100854451 6054856769557395151281677)
                ·
                  refine ⟨2270571288584023181730629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6054856769557395151281677 2270571288584023181730629)
                  ·
                    refine ⟨425732116609504346574493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2270571288584023181730629 425732116609504346574493)
                    ·
                      rfl

theorem cell23_2487331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 4].length) (baseStart_2487331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487331 prefixEnd_2487331 := by exact prefixLift 2487331
  have htrace : WordTrace (prefixWord ++ tailWord_2487331) baseStart_2487331 baseEnd_2487331 := by
    simpa [prefixWord, tailWord_2487331, baseEnd_2487331] using wordTrace_append hprefix tailTrace_2487331
  have hstable : (prefixWord ++ tailWord_2487331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487331).length < 2 ^ (prefixWord ++ tailWord_2487331).sum := by decide
  have hdescent : baseEnd_2487331 < baseStart_2487331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487347 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 6]
def baseStart_2487347 : Nat := 118140960795 + 2487347 * 2 ^ 59
def prefixEnd_2487347 : Nat := 4983230072969 + 3 ^ 40 * 2487347 * 2
def baseEnd_2487347 : Nat := 1277204565518984977123405

theorem tailTrace_2487347 : CollatzResearch.WordTrace tailWord_2487347 prefixEnd_2487347 1277204565518984977123405 := by
  unfold tailWord_2487347
  simp only [CollatzResearch.WordTrace]
  refine ⟨90720998119774098892252295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60480665413182732594834863 90720998119774098892252295)
  ·
    refine ⟨136081497179661148338378443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90720998119774098892252295 136081497179661148338378443)
    ·
      refine ⟨204122245769491722507567665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136081497179661148338378443 204122245769491722507567665)
      ·
        refine ⟨153091684327118791880675749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204122245769491722507567665 153091684327118791880675749)
        ·
          refine ⟨28704690811334773477626703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153091684327118791880675749 28704690811334773477626703)
          ·
            refine ⟨43057036217002160216440055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28704690811334773477626703 43057036217002160216440055)
            ·
              refine ⟨64585554325503240324660083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43057036217002160216440055 64585554325503240324660083)
              ·
                refine ⟨96878331488254860486990125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64585554325503240324660083 96878331488254860486990125)
                ·
                  refine ⟨36329374308095572682621297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96878331488254860486990125 36329374308095572682621297)
                  ·
                    refine ⟨27247030731071679511965973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36329374308095572682621297 27247030731071679511965973)
                    ·
                      refine ⟨1277204565518984977123405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27247030731071679511965973 1277204565518984977123405)
                      ·
                        rfl

theorem cell23_2487347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_2487347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487347 prefixEnd_2487347 := by exact prefixLift 2487347
  have htrace : WordTrace (prefixWord ++ tailWord_2487347) baseStart_2487347 baseEnd_2487347 := by
    simpa [prefixWord, tailWord_2487347, baseEnd_2487347] using wordTrace_append hprefix tailTrace_2487347
  have hstable : (prefixWord ++ tailWord_2487347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487347).length < 2 ^ (prefixWord ++ tailWord_2487347).sum := by decide
  have hdescent : baseEnd_2487347 < baseStart_2487347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487348 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 3, 4]
def baseStart_2487348 : Nat := 118140960795 + 2487348 * 2 ^ 59
def prefixEnd_2487348 : Nat := 4983230072969 + 3 ^ 40 * 2487348 * 2
def baseEnd_2487348 : Nat := 425735026333213157736967

theorem tailTrace_2487348 : CollatzResearch.WordTrace tailWord_2487348 prefixEnd_2487348 425735026333213157736967 := by
  unfold tailWord_2487348
  simp only [CollatzResearch.WordTrace]
  refine ⟨45360517296385238031519349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60480689728513650708692465 45360517296385238031519349)
  ·
    refine ⟨4252548496536116065454939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45360517296385238031519349 4252548496536116065454939)
    ·
      refine ⟨6378822744804174098182409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4252548496536116065454939 6378822744804174098182409)
      ·
        refine ⟨4784117058603130573636807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6378822744804174098182409 4784117058603130573636807)
        ·
          refine ⟨7176175587904695860455211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4784117058603130573636807 7176175587904695860455211)
          ·
            refine ⟨10764263381857043790682817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7176175587904695860455211 10764263381857043790682817)
            ·
              refine ⟨8073197536392782843012113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10764263381857043790682817 8073197536392782843012113)
              ·
                refine ⟨6054898152294587132259085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8073197536392782843012113 6054898152294587132259085)
                ·
                  refine ⟨2270586807110470174597157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6054898152294587132259085 2270586807110470174597157)
                  ·
                    refine ⟨425735026333213157736967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2270586807110470174597157 425735026333213157736967)
                    ·
                      rfl

theorem cell23_2487348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_2487348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487348 prefixEnd_2487348 := by exact prefixLift 2487348
  have htrace : WordTrace (prefixWord ++ tailWord_2487348) baseStart_2487348 baseEnd_2487348 := by
    simpa [prefixWord, tailWord_2487348, baseEnd_2487348] using wordTrace_append hprefix tailTrace_2487348
  have hstable : (prefixWord ++ tailWord_2487348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487348).length < 2 ^ (prefixWord ++ tailWord_2487348).sum := by decide
  have hdescent : baseEnd_2487348 < baseStart_2487348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487382 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_2487382 : Nat := 118140960795 + 2487382 * 2 ^ 59
def prefixEnd_2487382 : Nat := 4983230072969 + 3 ^ 40 * 2487382 * 2
def baseEnd_2487382 : Nat := 425740845780630780061915

theorem tailTrace_2487382 : CollatzResearch.WordTrace tailWord_2487382 prefixEnd_2487382 425740845780630780061915 := by
  unfold tailWord_2487382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5670142167165456241861025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60481516449764866579850933 5670142167165456241861025)
  ·
    refine ⟨4252606625374092181395769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5670142167165456241861025 4252606625374092181395769)
    ·
      refine ⟨3189454969030569136046827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4252606625374092181395769 3189454969030569136046827)
      ·
        refine ⟨4784182453545853704070241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3189454969030569136046827 4784182453545853704070241)
        ·
          refine ⟨3588136840159390278052681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4784182453545853704070241 3588136840159390278052681)
          ·
            refine ⟨2691102630119542708539511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3588136840159390278052681 2691102630119542708539511)
            ·
              refine ⟨4036653945179314062809267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2691102630119542708539511 4036653945179314062809267)
              ·
                refine ⟨6054980917768971094213901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4036653945179314062809267 6054980917768971094213901)
                ·
                  refine ⟨2270617844163364160330213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6054980917768971094213901 2270617844163364160330213)
                  ·
                    refine ⟨425740845780630780061915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2270617844163364160330213 425740845780630780061915)
                    ·
                      rfl

theorem cell23_2487382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_2487382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487382 prefixEnd_2487382 := by exact prefixLift 2487382
  have htrace : WordTrace (prefixWord ++ tailWord_2487382) baseStart_2487382 baseEnd_2487382 := by
    simpa [prefixWord, tailWord_2487382, baseEnd_2487382] using wordTrace_append hprefix tailTrace_2487382
  have hstable : (prefixWord ++ tailWord_2487382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487382).length < 2 ^ (prefixWord ++ tailWord_2487382).sum := by decide
  have hdescent : baseEnd_2487382 < baseStart_2487382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487404 : List Nat := [2, 2, 1, 1, 3, 2, 2, 3, 1, 6]
def baseStart_2487404 : Nat := 118140960795 + 2487404 * 2 ^ 59
def prefixEnd_2487404 : Nat := 4983230072969 + 3 ^ 40 * 2487404 * 2
def baseEnd_2487404 : Nat := 425744611305430418036881

theorem tailTrace_2487404 : CollatzResearch.WordTrace tailWord_2487404 prefixEnd_2487404 425744611305430418036881 := by
  unfold tailWord_2487404
  simp only [CollatzResearch.WordTrace]
  refine ⟨45361538540283798813538633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60482051387045065084718177 45361538540283798813538633)
  ·
    refine ⟨34021153905212849110153975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45361538540283798813538633 34021153905212849110153975)
    ·
      refine ⟨51031730857819273665230963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34021153905212849110153975 51031730857819273665230963)
      ·
        refine ⟨76547596286728910497846445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51031730857819273665230963 76547596286728910497846445)
        ·
          refine ⟨28705348607523341436692417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76547596286728910497846445 28705348607523341436692417)
          ·
            refine ⟨21529011455642506077519313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28705348607523341436692417 21529011455642506077519313)
            ·
              refine ⟨16146758591731879558139485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21529011455642506077519313 16146758591731879558139485)
              ·
                refine ⟨6055034471899454834302307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16146758591731879558139485 6055034471899454834302307)
                ·
                  refine ⟨9082551707849182251453461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6055034471899454834302307 9082551707849182251453461)
                  ·
                    refine ⟨425744611305430418036881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9082551707849182251453461 425744611305430418036881)
                    ·
                      rfl

theorem cell23_2487404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_2487404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487404 prefixEnd_2487404 := by exact prefixLift 2487404
  have htrace : WordTrace (prefixWord ++ tailWord_2487404) baseStart_2487404 baseEnd_2487404 := by
    simpa [prefixWord, tailWord_2487404, baseEnd_2487404] using wordTrace_append hprefix tailTrace_2487404
  have hstable : (prefixWord ++ tailWord_2487404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487404).length < 2 ^ (prefixWord ++ tailWord_2487404).sum := by decide
  have hdescent : baseEnd_2487404 < baseStart_2487404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487424 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 4]
def baseStart_2487424 : Nat := 118140960795 + 2487424 * 2 ^ 59
def prefixEnd_2487424 : Nat := 4983230072969 + 3 ^ 40 * 2487424 * 2
def baseEnd_2487424 : Nat := 1277244103529381175860551

theorem tailTrace_2487424 : CollatzResearch.WordTrace tailWord_2487424 prefixEnd_2487424 1277244103529381175860551 := by
  unfold tailWord_2487424
  simp only [CollatzResearch.WordTrace]
  refine ⟨45361903270247570521402663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60482537693663427361870217 45361903270247570521402663)
  ·
    refine ⟨68042854905371355782103995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45361903270247570521402663 68042854905371355782103995)
    ·
      refine ⟨102064282358057033673155993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68042854905371355782103995 102064282358057033673155993)
      ·
        refine ⟨76548211768542775254866995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102064282358057033673155993 76548211768542775254866995)
        ·
          refine ⟨114822317652814162882300493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76548211768542775254866995 114822317652814162882300493)
          ·
            refine ⟨43058369119805311080862685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114822317652814162882300493 43058369119805311080862685)
            ·
              refine ⟨16146888419926991655323507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43058369119805311080862685 16146888419926991655323507)
              ·
                refine ⟨24220332629890487482985261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16146888419926991655323507 24220332629890487482985261)
                ·
                  refine ⟨9082624736208932806119473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24220332629890487482985261 9082624736208932806119473)
                  ·
                    refine ⟨6811968552156699604589605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9082624736208932806119473 6811968552156699604589605)
                    ·
                      refine ⟨1277244103529381175860551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6811968552156699604589605 1277244103529381175860551)
                      ·
                        rfl

theorem cell23_2487424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_2487424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487424 prefixEnd_2487424 := by exact prefixLift 2487424
  have htrace : WordTrace (prefixWord ++ tailWord_2487424) baseStart_2487424 baseEnd_2487424 := by
    simpa [prefixWord, tailWord_2487424, baseEnd_2487424] using wordTrace_append hprefix tailTrace_2487424
  have hstable : (prefixWord ++ tailWord_2487424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487424).length < 2 ^ (prefixWord ++ tailWord_2487424).sum := by decide
  have hdescent : baseEnd_2487424 < baseStart_2487424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487438 : List Nat := [4, 1, 1, 3, 2, 1, 1, 4, 2, 4]
def baseStart_2487438 : Nat := 118140960795 + 2487438 * 2 ^ 59
def prefixEnd_2487438 : Nat := 4983230072969 + 3 ^ 40 * 2487438 * 2
def baseEnd_2487438 : Nat := 425750430752848040361829

theorem tailTrace_2487438 : CollatzResearch.WordTrace tailWord_2487438 prefixEnd_2487438 425750430752848040361829 := by
  unfold tailWord_2487438
  simp only [CollatzResearch.WordTrace]
  refine ⟨11340539645305552679226871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60482878108296280955876645 11340539645305552679226871)
  ·
    refine ⟨17010809467958329018840307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11340539645305552679226871 17010809467958329018840307)
    ·
      refine ⟨25516214201937493528260461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17010809467958329018840307 25516214201937493528260461)
      ·
        refine ⟨9568580325726560073097673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25516214201937493528260461 9568580325726560073097673)
        ·
          refine ⟨7176435244294920054823255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9568580325726560073097673 7176435244294920054823255)
          ·
            refine ⟨10764652866442380082234883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7176435244294920054823255 10764652866442380082234883)
            ·
              refine ⟨16146979299663570123352325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10764652866442380082234883 16146979299663570123352325)
              ·
                refine ⟨3027558618686919398128561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16146979299663570123352325 3027558618686919398128561)
                ·
                  refine ⟨2270668964015189548596421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3027558618686919398128561 2270668964015189548596421)
                  ·
                    refine ⟨425750430752848040361829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2270668964015189548596421 425750430752848040361829)
                    ·
                      rfl

theorem cell23_2487438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_2487438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487438 prefixEnd_2487438 := by exact prefixLift 2487438
  have htrace : WordTrace (prefixWord ++ tailWord_2487438) baseStart_2487438 baseEnd_2487438 := by
    simpa [prefixWord, tailWord_2487438, baseEnd_2487438] using wordTrace_append hprefix tailTrace_2487438
  have hstable : (prefixWord ++ tailWord_2487438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487438).length < 2 ^ (prefixWord ++ tailWord_2487438).sum := by decide
  have hdescent : baseEnd_2487438 < baseStart_2487438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487461 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 1, 3, 3]
def baseStart_2487461 : Nat := 118140960795 + 2487461 * 2 ^ 59
def prefixEnd_2487461 : Nat := 4983230072969 + 3 ^ 40 * 2487461 * 2
def baseEnd_2487461 : Nat := 1277263102313597531097881

theorem tailTrace_2487461 : CollatzResearch.WordTrace tailWord_2487461 prefixEnd_2487461 1277263102313597531097881 := by
  unfold tailWord_2487461
  simp only [CollatzResearch.WordTrace]
  refine ⟨90725156041361096361902237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60483437360907397574601491 90725156041361096361902237)
  ·
    refine ⟨34021933515510411135713339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90725156041361096361902237 34021933515510411135713339)
    ·
      refine ⟨51032900273265616703570009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34021933515510411135713339 51032900273265616703570009)
      ·
        refine ⟨38274675204949212527677507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51032900273265616703570009 38274675204949212527677507)
        ·
          refine ⟨57412012807423818791516261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38274675204949212527677507 57412012807423818791516261)
          ·
            refine ⟨10764752401391966023409299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57412012807423818791516261 10764752401391966023409299)
            ·
              refine ⟨16147128602087949035113949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10764752401391966023409299 16147128602087949035113949)
              ·
                refine ⟨6055173225782980888167731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16147128602087949035113949 6055173225782980888167731)
                ·
                  refine ⟨9082759838674471332251597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6055173225782980888167731 9082759838674471332251597)
                  ·
                    refine ⟨3406034939502926749594349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9082759838674471332251597 3406034939502926749594349)
                    ·
                      refine ⟨1277263102313597531097881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3406034939502926749594349 1277263102313597531097881)
                      ·
                        rfl

theorem cell23_2487461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_2487461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487461 prefixEnd_2487461 := by exact prefixLift 2487461
  have htrace : WordTrace (prefixWord ++ tailWord_2487461) baseStart_2487461 baseEnd_2487461 := by
    simpa [prefixWord, tailWord_2487461, baseEnd_2487461] using wordTrace_append hprefix tailTrace_2487461
  have hstable : (prefixWord ++ tailWord_2487461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487461).length < 2 ^ (prefixWord ++ tailWord_2487461).sum := by decide
  have hdescent : baseEnd_2487461 < baseStart_2487461 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487512 : List Nat := [2, 1, 2, 2, 5, 1, 3, 1, 2, 1, 3]
def baseStart_2487512 : Nat := 118140960795 + 2487512 * 2 ^ 59
def prefixEnd_2487512 : Nat := 4983230072969 + 3 ^ 40 * 2487512 * 2
def baseEnd_2487512 : Nat := 1277289289826976831560147

theorem tailTrace_2487512 : CollatzResearch.WordTrace tailWord_2487512 prefixEnd_2487512 1277289289826976831560147 := by
  unfold tailWord_2487512
  simp only [CollatzResearch.WordTrace]
  refine ⟨45363508082088166036004395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60484677442784221381339193 45363508082088166036004395)
  ·
    refine ⟨68045262123132249054006593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45363508082088166036004395 68045262123132249054006593)
    ·
      refine ⟨51033946592349186790504945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68045262123132249054006593 51033946592349186790504945)
      ·
        refine ⟨38275459944261890092878709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51033946592349186790504945 38275459944261890092878709)
        ·
          refine ⟨3588324369774552196207379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38275459944261890092878709 3588324369774552196207379)
          ·
            refine ⟨5382486554661828294311069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3588324369774552196207379 5382486554661828294311069)
            ·
              refine ⟨2018432457998185610366651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5382486554661828294311069 2018432457998185610366651)
              ·
                refine ⟨3027648686997278415549977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018432457998185610366651 3027648686997278415549977)
                ·
                  refine ⟨2270736515247958811662483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3027648686997278415549977 2270736515247958811662483)
                  ·
                    refine ⟨3406104772871938217493725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2270736515247958811662483 3406104772871938217493725)
                    ·
                      refine ⟨1277289289826976831560147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3406104772871938217493725 1277289289826976831560147)
                      ·
                        rfl

theorem cell23_2487512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_2487512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487512 prefixEnd_2487512 := by exact prefixLift 2487512
  have htrace : WordTrace (prefixWord ++ tailWord_2487512) baseStart_2487512 baseEnd_2487512 := by
    simpa [prefixWord, tailWord_2487512, baseEnd_2487512] using wordTrace_append hprefix tailTrace_2487512
  have hstable : (prefixWord ++ tailWord_2487512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487512).length < 2 ^ (prefixWord ++ tailWord_2487512).sum := by decide
  have hdescent : baseEnd_2487512 < baseStart_2487512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487538 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 2, 1, 5]
def baseStart_2487538 : Nat := 118140960795 + 2487538 * 2 ^ 59
def prefixEnd_2487538 : Nat := 4983230072969 + 3 ^ 40 * 2487538 * 2
def baseEnd_2487538 : Nat := 1277302640323993729835027

theorem tailTrace_2487538 : CollatzResearch.WordTrace tailWord_2487538 prefixEnd_2487538 1277302640323993729835027 := by
  unfold tailWord_2487538
  simp only [CollatzResearch.WordTrace]
  refine ⟨22681991115520534628113817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60485309641388092341636845 22681991115520534628113817)
  ·
    refine ⟨17011493336640400971085363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22681991115520534628113817 17011493336640400971085363)
    ·
      refine ⟨25517240004960601456628045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17011493336640400971085363 25517240004960601456628045)
      ·
        refine ⟨9568965001860225546235517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25517240004960601456628045 9568965001860225546235517)
        ·
          refine ⟨3588361875697584579838319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9568965001860225546235517 3588361875697584579838319)
          ·
            refine ⟨5382542813546376869757479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3588361875697584579838319 5382542813546376869757479)
            ·
              refine ⟨8073814220319565304636219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5382542813546376869757479 8073814220319565304636219)
              ·
                refine ⟨12110721330479347956954329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8073814220319565304636219 12110721330479347956954329)
                ·
                  refine ⟨9083040997859510967715747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12110721330479347956954329 9083040997859510967715747)
                  ·
                    refine ⟨13624561496789266451573621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9083040997859510967715747 13624561496789266451573621)
                    ·
                      refine ⟨1277302640323993729835027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13624561496789266451573621 1277302640323993729835027)
                      ·
                        rfl

theorem cell23_2487538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_2487538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487538 prefixEnd_2487538 := by exact prefixLift 2487538
  have htrace : WordTrace (prefixWord ++ tailWord_2487538) baseStart_2487538 baseEnd_2487538 := by
    simpa [prefixWord, tailWord_2487538, baseEnd_2487538] using wordTrace_append hprefix tailTrace_2487538
  have hstable : (prefixWord ++ tailWord_2487538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487538).length < 2 ^ (prefixWord ++ tailWord_2487538).sum := by decide
  have hdescent : baseEnd_2487538 < baseStart_2487538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487544 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 6]
def baseStart_2487544 : Nat := 118140960795 + 2487544 * 2 ^ 59
def prefixEnd_2487544 : Nat := 4983230072969 + 3 ^ 40 * 2487544 * 2
def baseEnd_2487544 : Nat := 1277305721207920706359999

theorem tailTrace_2487544 : CollatzResearch.WordTrace tailWord_2487544 prefixEnd_2487544 1277305721207920706359999 := by
  unfold tailWord_2487544
  simp only [CollatzResearch.WordTrace]
  refine ⟨45364091650030200768586843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60485455533373601024782457 45364091650030200768586843)
  ·
    refine ⟨68046137475045301152880265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45364091650030200768586843 68046137475045301152880265)
    ·
      refine ⟨51034603106283975864660199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68046137475045301152880265 51034603106283975864660199)
      ·
        refine ⟨76551904659425963796990299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51034603106283975864660199 76551904659425963796990299)
        ·
          refine ⟨114827856989138945695485449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76551904659425963796990299 114827856989138945695485449)
          ·
            refine ⟨86120892741854209271614087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114827856989138945695485449 86120892741854209271614087)
            ·
              refine ⟨129181339112781313907421131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86120892741854209271614087 129181339112781313907421131)
              ·
                refine ⟨193772008669171970861131697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129181339112781313907421131 193772008669171970861131697)
                ·
                  refine ⟨145329006501878978145848773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193772008669171970861131697 145329006501878978145848773)
                  ·
                    refine ⟨27249188719102308402346645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 145329006501878978145848773 27249188719102308402346645)
                    ·
                      refine ⟨1277305721207920706359999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27249188719102308402346645 1277305721207920706359999)
                      ·
                        rfl

theorem cell23_2487544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_2487544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487544 prefixEnd_2487544 := by exact prefixLift 2487544
  have htrace : WordTrace (prefixWord ++ tailWord_2487544) baseStart_2487544 baseEnd_2487544 := by
    simpa [prefixWord, tailWord_2487544, baseEnd_2487544] using wordTrace_append hprefix tailTrace_2487544
  have hstable : (prefixWord ++ tailWord_2487544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487544).length < 2 ^ (prefixWord ++ tailWord_2487544).sum := by decide
  have hdescent : baseEnd_2487544 < baseStart_2487544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487588 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 2, 5]
def baseStart_2487588 : Nat := 118140960795 + 2487588 * 2 ^ 59
def prefixEnd_2487588 : Nat := 4983230072969 + 3 ^ 40 * 2487588 * 2
def baseEnd_2487588 : Nat := 425776104785572844736599

theorem tailTrace_2487588 : CollatzResearch.WordTrace tailWord_2487588 prefixEnd_2487588 425776104785572844736599 := by
  unfold tailWord_2487588
  simp only [CollatzResearch.WordTrace]
  refine ⟨45364894055950498525887709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60486525407933998034516945 45364894055950498525887709)
  ·
    refine ⟨17011835270981436947207891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45364894055950498525887709 17011835270981436947207891)
    ·
      refine ⟨25517752906472155420811837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17011835270981436947207891 25517752906472155420811837)
      ·
        refine ⟨9569157339927058282804439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25517752906472155420811837 9569157339927058282804439)
        ·
          refine ⟨14353736009890587424206659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9569157339927058282804439 14353736009890587424206659)
          ·
            refine ⟨21530604014835881136309989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14353736009890587424206659 21530604014835881136309989)
            ·
              refine ⟨4036988252781727713058123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21530604014835881136309989 4036988252781727713058123)
              ·
                refine ⟨6055482379172591569587185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4036988252781727713058123 6055482379172591569587185)
                ·
                  refine ⟨4541611784379443677190389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6055482379172591569587185 4541611784379443677190389)
                  ·
                    refine ⟨425776104785572844736599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4541611784379443677190389 425776104785572844736599)
                    ·
                      rfl

theorem cell23_2487588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_2487588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487588 prefixEnd_2487588 := by exact prefixLift 2487588
  have htrace : WordTrace (prefixWord ++ tailWord_2487588) baseStart_2487588 baseEnd_2487588 := by
    simpa [prefixWord, tailWord_2487588, baseEnd_2487588] using wordTrace_append hprefix tailTrace_2487588
  have hstable : (prefixWord ++ tailWord_2487588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487588).length < 2 ^ (prefixWord ++ tailWord_2487588).sum := by decide
  have hdescent : baseEnd_2487588 < baseStart_2487588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487608 : List Nat := [2, 1, 2, 1, 3, 1, 1, 4, 2, 4, 2]
def baseStart_2487608 : Nat := 118140960795 + 2487608 * 2 ^ 59
def prefixEnd_2487608 : Nat := 4983230072969 + 3 ^ 40 * 2487608 * 2
def baseEnd_2487608 : Nat := 1277338583969808455959705

theorem tailTrace_2487608 : CollatzResearch.WordTrace tailWord_2487608 prefixEnd_2487608 1277338583969808455959705 := by
  unfold tailWord_2487608
  simp only [CollatzResearch.WordTrace]
  refine ⟨45365258785914270233751739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60487011714552360311668985 45365258785914270233751739)
  ·
    refine ⟨68047888178871405350627609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45365258785914270233751739 68047888178871405350627609)
    ·
      refine ⟨51035916134153554012970707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68047888178871405350627609 51035916134153554012970707)
      ·
        refine ⟨76553874201230331019456061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51035916134153554012970707 76553874201230331019456061)
        ·
          refine ⟨28707702825461374132296023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76553874201230331019456061 28707702825461374132296023)
          ·
            refine ⟨43061554238192061198444035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28707702825461374132296023 43061554238192061198444035)
            ·
              refine ⟨64592331357288091797666053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43061554238192061198444035 64592331357288091797666053)
              ·
                refine ⟨12111062129491517212062385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64592331357288091797666053 12111062129491517212062385)
                ·
                  refine ⟨9083296597118637909046789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12111062129491517212062385 9083296597118637909046789)
                  ·
                    refine ⟨1703118111959744607946273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9083296597118637909046789 1703118111959744607946273)
                    ·
                      refine ⟨1277338583969808455959705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1703118111959744607946273 1277338583969808455959705)
                      ·
                        rfl

theorem cell23_2487608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 4, 2, 4, 2].length) (baseStart_2487608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487608 prefixEnd_2487608 := by exact prefixLift 2487608
  have htrace : WordTrace (prefixWord ++ tailWord_2487608) baseStart_2487608 baseEnd_2487608 := by
    simpa [prefixWord, tailWord_2487608, baseEnd_2487608] using wordTrace_append hprefix tailTrace_2487608
  have hstable : (prefixWord ++ tailWord_2487608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487608).length < 2 ^ (prefixWord ++ tailWord_2487608).sum := by decide
  have hdescent : baseEnd_2487608 < baseStart_2487608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487609 : List Nat := [1, 2, 1, 6, 3, 1, 2, 2, 5]
def baseStart_2487609 : Nat := 118140960795 + 2487609 * 2 ^ 59
def prefixEnd_2487609 : Nat := 4983230072969 + 3 ^ 40 * 2487609 * 2
def baseEnd_2487609 : Nat := 141926566383384772449689

theorem tailTrace_2487609 : CollatzResearch.WordTrace tailWord_2487609 prefixEnd_2487609 141926566383384772449689 := by
  unfold tailWord_2487609
  simp only [CollatzResearch.WordTrace]
  refine ⟨90730554044824917638289881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60487036029883278425526587 90730554044824917638289881)
  ·
    refine ⟨68047915533618688228717411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90730554044824917638289881 68047915533618688228717411)
    ·
      refine ⟨102071873300428032343076117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68047915533618688228717411 102071873300428032343076117)
      ·
        refine ⟨4784619060957564016081693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102071873300428032343076117 4784619060957564016081693)
        ·
          refine ⟨1794232147859086506030635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4784619060957564016081693 1794232147859086506030635)
          ·
            refine ⟨2691348221788629759045953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1794232147859086506030635 2691348221788629759045953)
            ·
              refine ⟨2018511166341472319284465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2691348221788629759045953 2018511166341472319284465)
              ·
                refine ⟨1513883374756104239463349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2018511166341472319284465 1513883374756104239463349)
                ·
                  refine ⟨141926566383384772449689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1513883374756104239463349 141926566383384772449689)
                  ·
                    rfl

theorem cell23_2487609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 2, 2, 5].length) (baseStart_2487609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487609 prefixEnd_2487609 := by exact prefixLift 2487609
  have htrace : WordTrace (prefixWord ++ tailWord_2487609) baseStart_2487609 baseEnd_2487609 := by
    simpa [prefixWord, tailWord_2487609, baseEnd_2487609] using wordTrace_append hprefix tailTrace_2487609
  have hstable : (prefixWord ++ tailWord_2487609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487609).length < 2 ^ (prefixWord ++ tailWord_2487609).sum := by decide
  have hdescent : baseEnd_2487609 < baseStart_2487609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487652 : List Nat := [2, 3, 1, 1, 3, 3, 2, 3, 1, 4]
def baseStart_2487652 : Nat := 118140960795 + 2487652 * 2 ^ 59
def prefixEnd_2487652 : Nat := 4983230072969 + 3 ^ 40 * 2487652 * 2
def baseEnd_2487652 : Nat := 425787059039535427936501

theorem tailTrace_2487652 : CollatzResearch.WordTrace tailWord_2487652 prefixEnd_2487652 425787059039535427936501 := by
  unfold tailWord_2487652
  simp only [CollatzResearch.WordTrace]
  refine ⟨45366061191834567991052605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60488081589112757321403473 45366061191834567991052605)
  ·
    refine ⟨17012272946937962996644727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45366061191834567991052605 17012272946937962996644727)
    ·
      refine ⟨25518409420406944494967091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17012272946937962996644727 25518409420406944494967091)
      ·
        refine ⟨38277614130610416742450637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25518409420406944494967091 38277614130610416742450637)
        ·
          refine ⟨14354105298978906278418989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38277614130610416742450637 14354105298978906278418989)
          ·
            refine ⟨5382789487117089854407121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14354105298978906278418989 5382789487117089854407121)
            ·
              refine ⟨4037092115337817390805341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5382789487117089854407121 4037092115337817390805341)
              ·
                refine ⟨1513909543251681521552003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4037092115337817390805341 1513909543251681521552003)
                ·
                  refine ⟨2270864314877522282328005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1513909543251681521552003 2270864314877522282328005)
                  ·
                    refine ⟨425787059039535427936501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2270864314877522282328005 425787059039535427936501)
                    ·
                      rfl

theorem cell23_2487652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_2487652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487652 prefixEnd_2487652 := by exact prefixLift 2487652
  have htrace : WordTrace (prefixWord ++ tailWord_2487652) baseStart_2487652 baseEnd_2487652 := by
    simpa [prefixWord, tailWord_2487652, baseEnd_2487652] using wordTrace_append hprefix tailTrace_2487652
  have hstable : (prefixWord ++ tailWord_2487652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487652).length < 2 ^ (prefixWord ++ tailWord_2487652).sum := by decide
  have hdescent : baseEnd_2487652 < baseStart_2487652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487675 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 3, 1, 3]
def baseStart_2487675 : Nat := 118140960795 + 2487675 * 2 ^ 59
def prefixEnd_2487675 : Nat := 4983230072969 + 3 ^ 40 * 2487675 * 2
def baseEnd_2487675 : Nat := 1277372987173659693821897

theorem tailTrace_2487675 : CollatzResearch.WordTrace tailWord_2487675 prefixEnd_2487675 1277372987173659693821897 := by
  unfold tailWord_2487675
  simp only [CollatzResearch.WordTrace]
  refine ⟨90732961262585810910192479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60488640841723873940128319 90732961262585810910192479)
  ·
    refine ⟨136099441893878716365288719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90732961262585810910192479 136099441893878716365288719)
    ·
      refine ⟨204149162840818074547933079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136099441893878716365288719 204149162840818074547933079)
      ·
        refine ⟨306223744261227111821899619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204149162840818074547933079 306223744261227111821899619)
        ·
          refine ⟨459335616391840667732849429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306223744261227111821899619 459335616391840667732849429)
          ·
            refine ⟨21531357018367531299977317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 459335616391840667732849429 21531357018367531299977317)
            ·
              refine ⟨4037129440943912118745747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21531357018367531299977317 4037129440943912118745747)
              ·
                refine ⟨6055694161415868178118621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4037129440943912118745747 6055694161415868178118621)
                ·
                  refine ⟨2270885310530950566794483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6055694161415868178118621 2270885310530950566794483)
                  ·
                    refine ⟨3406327965796425850191725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2270885310530950566794483 3406327965796425850191725)
                    ·
                      refine ⟨1277372987173659693821897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3406327965796425850191725 1277372987173659693821897)
                      ·
                        rfl

theorem cell23_2487675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 1, 3].length) (baseStart_2487675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487675 prefixEnd_2487675 := by exact prefixLift 2487675
  have htrace : WordTrace (prefixWord ++ tailWord_2487675) baseStart_2487675 baseEnd_2487675 := by
    simpa [prefixWord, tailWord_2487675, baseEnd_2487675] using wordTrace_append hprefix tailTrace_2487675
  have hstable : (prefixWord ++ tailWord_2487675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487675).length < 2 ^ (prefixWord ++ tailWord_2487675).sum := by decide
  have hdescent : baseEnd_2487675 < baseStart_2487675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487709 : List Nat := [1, 4, 2, 1, 3, 1, 3, 3, 1, 1, 3]
def baseStart_2487709 : Nat := 118140960795 + 2487709 * 2 ^ 59
def prefixEnd_2487709 : Nat := 4983230072969 + 3 ^ 40 * 2487709 * 2
def baseEnd_2487709 : Nat := 1277390445515912560796741

theorem tailTrace_2487709 : CollatzResearch.WordTrace tailWord_2487709 prefixEnd_2487709 1277390445515912560796741 := by
  unfold tailWord_2487709
  simp only [CollatzResearch.WordTrace]
  refine ⟨90734201344462634716930181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60489467562975089811286787 90734201344462634716930181)
  ·
    refine ⟨17012662752086744009424409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90734201344462634716930181 17012662752086744009424409)
    ·
      refine ⟨12759497064065058007068307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17012662752086744009424409 12759497064065058007068307)
      ·
        refine ⟨19139245596097587010602461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12759497064065058007068307 19139245596097587010602461)
        ·
          refine ⟨7177217098536595128975923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19139245596097587010602461 7177217098536595128975923)
          ·
            refine ⟨10765825647804892693463885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7177217098536595128975923 10765825647804892693463885)
            ·
              refine ⟨4037184617926834760048957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10765825647804892693463885 4037184617926834760048957)
              ·
                refine ⟨1513944231722563035018359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4037184617926834760048957 1513944231722563035018359)
                ·
                  refine ⟨2270916347583844552527539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1513944231722563035018359 2270916347583844552527539)
                  ·
                    refine ⟨3406374521375766828791309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2270916347583844552527539 3406374521375766828791309)
                    ·
                      refine ⟨1277390445515912560796741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3406374521375766828791309 1277390445515912560796741)
                      ·
                        rfl

theorem cell23_2487709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_2487709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487709 prefixEnd_2487709 := by exact prefixLift 2487709
  have htrace : WordTrace (prefixWord ++ tailWord_2487709) baseStart_2487709 baseEnd_2487709 := by
    simpa [prefixWord, tailWord_2487709, baseEnd_2487709] using wordTrace_append hprefix tailTrace_2487709
  have hstable : (prefixWord ++ tailWord_2487709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487709).length < 2 ^ (prefixWord ++ tailWord_2487709).sum := by decide
  have hdescent : baseEnd_2487709 < baseStart_2487709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487746 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_2487746 : Nat := 118140960795 + 2487746 * 2 ^ 59
def prefixEnd_2487746 : Nat := 4983230072969 + 3 ^ 40 * 2487746 * 2
def baseEnd_2487746 : Nat := 425803148100042972011357

theorem tailTrace_2487746 : CollatzResearch.WordTrace tailWord_2487746 prefixEnd_2487746 425803148100042972011357 := by
  unfold tailWord_2487746
  simp only [CollatzResearch.WordTrace]
  refine ⟨22683887711332147509006773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60490367230219060024018061 22683887711332147509006773)
  ·
    refine ⟨2126614472937388828969385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22683887711332147509006773 2126614472937388828969385)
    ·
      refine ⟨1594960854703041621727039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2126614472937388828969385 1594960854703041621727039)
      ·
        refine ⟨2392441282054562432590559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1594960854703041621727039 2392441282054562432590559)
        ·
          refine ⟨3588661923081843648885839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2392441282054562432590559 3588661923081843648885839)
          ·
            refine ⟨5382992884622765473328759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3588661923081843648885839 5382992884622765473328759)
            ·
              refine ⟨8074489326934148209993139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5382992884622765473328759 8074489326934148209993139)
              ·
                refine ⟨12111733990401222314989709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8074489326934148209993139 12111733990401222314989709)
                ·
                  refine ⟨4541900246400458368121141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12111733990401222314989709 4541900246400458368121141)
                  ·
                    refine ⟨425803148100042972011357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4541900246400458368121141 425803148100042972011357)
                    ·
                      rfl

theorem cell23_2487746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_2487746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487746 prefixEnd_2487746 := by exact prefixLift 2487746
  have htrace : WordTrace (prefixWord ++ tailWord_2487746) baseStart_2487746 baseEnd_2487746 := by
    simpa [prefixWord, tailWord_2487746, baseEnd_2487746] using wordTrace_append hprefix tailTrace_2487746
  have hstable : (prefixWord ++ tailWord_2487746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487746).length < 2 ^ (prefixWord ++ tailWord_2487746).sum := by decide
  have hdescent : baseEnd_2487746 < baseStart_2487746 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487765 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 1, 3, 3]
def baseStart_2487765 : Nat := 118140960795 + 2487765 * 2 ^ 59
def prefixEnd_2487765 : Nat := 4983230072969 + 3 ^ 40 * 2487765 * 2
def baseEnd_2487765 : Nat := 1277419200432564341696483

theorem tailTrace_2487765 : CollatzResearch.WordTrace tailWord_2487765 prefixEnd_2487765 1277419200432564341696483 := by
  unfold tailWord_2487765
  simp only [CollatzResearch.WordTrace]
  refine ⟨90736243832259756280968749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60490829221506504187312499 90736243832259756280968749)
  ·
    refine ⟨34026091437097408605363281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90736243832259756280968749 34026091437097408605363281)
    ·
      refine ⟨25519568577823056454022461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34026091437097408605363281 25519568577823056454022461)
      ·
        refine ⟨9569838216683646170258423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25519568577823056454022461 9569838216683646170258423)
        ·
          refine ⟨14354757325025469255387635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9569838216683646170258423 14354757325025469255387635)
          ·
            refine ⟨21532135987538203883081453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14354757325025469255387635 21532135987538203883081453)
            ·
              refine ⟨8074550995326826456155545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21532135987538203883081453 8074550995326826456155545)
              ·
                refine ⟨6055913246495119842116659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8074550995326826456155545 6055913246495119842116659)
                ·
                  refine ⟨9083869869742679763174989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6055913246495119842116659 9083869869742679763174989)
                  ·
                    refine ⟨3406451201153504911190621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9083869869742679763174989 3406451201153504911190621)
                    ·
                      refine ⟨1277419200432564341696483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3406451201153504911190621 1277419200432564341696483)
                      ·
                        rfl

theorem cell23_2487765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_2487765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487765 prefixEnd_2487765 := by exact prefixLift 2487765
  have htrace : WordTrace (prefixWord ++ tailWord_2487765) baseStart_2487765 baseEnd_2487765 := by
    simpa [prefixWord, tailWord_2487765, baseEnd_2487765] using wordTrace_append hprefix tailTrace_2487765
  have hstable : (prefixWord ++ tailWord_2487765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487765).length < 2 ^ (prefixWord ++ tailWord_2487765).sum := by decide
  have hdescent : baseEnd_2487765 < baseStart_2487765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487771 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 10]
def baseStart_2487771 : Nat := 118140960795 + 2487771 * 2 ^ 59
def prefixEnd_2487771 : Nat := 4983230072969 + 3 ^ 40 * 2487771 * 2
def baseEnd_2487771 : Nat := 1277422281316491318221455

theorem tailTrace_2487771 : CollatzResearch.WordTrace tailWord_2487771 prefixEnd_2487771 1277422281316491318221455 := by
  unfold tailWord_2487771
  simp only [CollatzResearch.WordTrace]
  refine ⟨90736462670238019305687167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60490975113492012870458111 90736462670238019305687167)
  ·
    refine ⟨136104694005357028958530751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90736462670238019305687167 136104694005357028958530751)
    ·
      refine ⟨204157041008035543437796127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136104694005357028958530751 204157041008035543437796127)
      ·
        refine ⟨306235561512053315156694191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204157041008035543437796127 306235561512053315156694191)
        ·
          refine ⟨459353342268079972735041287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306235561512053315156694191 459353342268079972735041287)
          ·
            refine ⟨689030013402119959102561931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459353342268079972735041287 689030013402119959102561931)
            ·
              refine ⟨1033545020103179938653842897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689030013402119959102561931 1033545020103179938653842897)
              ·
                refine ⟨775158765077384953990382173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1033545020103179938653842897 775158765077384953990382173)
                ·
                  refine ⟨290684536904019357746393315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 775158765077384953990382173 290684536904019357746393315)
                  ·
                    refine ⟨436026805356029036619589973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 290684536904019357746393315 436026805356029036619589973)
                    ·
                      refine ⟨1277422281316491318221455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 436026805356029036619589973 1277422281316491318221455)
                      ·
                        rfl

theorem cell23_2487771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 10].length) (baseStart_2487771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487771 prefixEnd_2487771 := by exact prefixLift 2487771
  have htrace : WordTrace (prefixWord ++ tailWord_2487771) baseStart_2487771 baseEnd_2487771 := by
    simpa [prefixWord, tailWord_2487771, baseEnd_2487771] using wordTrace_append hprefix tailTrace_2487771
  have hstable : (prefixWord ++ tailWord_2487771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487771).length < 2 ^ (prefixWord ++ tailWord_2487771).sum := by decide
  have hdescent : baseEnd_2487771 < baseStart_2487771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487783 : List Nat := [1, 1, 5, 2, 1, 4, 2, 2, 1, 2, 2]
def baseStart_2487783 : Nat := 118140960795 + 2487783 * 2 ^ 59
def prefixEnd_2487783 : Nat := 4983230072969 + 3 ^ 40 * 2487783 * 2
def baseEnd_2487783 : Nat := 1277428443084345271271401

theorem tailTrace_2487783 : CollatzResearch.WordTrace tailWord_2487783 prefixEnd_2487783 1277428443084345271271401 := by
  unfold tailWord_2487783
  simp only [CollatzResearch.WordTrace]
  refine ⟨90736900346194545355124003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60491266897463030236749335 90736900346194545355124003)
  ·
    refine ⟨136105350519291818032686005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90736900346194545355124003 136105350519291818032686005)
    ·
      refine ⟨12759876611183607940564313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136105350519291818032686005 12759876611183607940564313)
      ·
        refine ⟨9569907458387705955423235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12759876611183607940564313 9569907458387705955423235)
        ·
          refine ⟨14354861187581558933134853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9569907458387705955423235 14354861187581558933134853)
          ·
            refine ⟨2691536472671542299962785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14354861187581558933134853 2691536472671542299962785)
            ·
              refine ⟨2018652354503656724972089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2691536472671542299962785 2018652354503656724972089)
              ·
                refine ⟨1513989265877742543729067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2018652354503656724972089 1513989265877742543729067)
                ·
                  refine ⟨2270983898816613815593601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1513989265877742543729067 2270983898816613815593601)
                  ·
                    refine ⟨1703237924112460361695201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2270983898816613815593601 1703237924112460361695201)
                    ·
                      refine ⟨1277428443084345271271401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1703237924112460361695201 1277428443084345271271401)
                      ·
                        rfl

theorem cell23_2487783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_2487783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487783 prefixEnd_2487783 := by exact prefixLift 2487783
  have htrace : WordTrace (prefixWord ++ tailWord_2487783) baseStart_2487783 baseEnd_2487783 := by
    simpa [prefixWord, tailWord_2487783, baseEnd_2487783] using wordTrace_append hprefix tailTrace_2487783
  have hstable : (prefixWord ++ tailWord_2487783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487783).length < 2 ^ (prefixWord ++ tailWord_2487783).sum := by decide
  have hdescent : baseEnd_2487783 < baseStart_2487783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487839 : List Nat := [1, 1, 2, 4, 1, 1, 5, 2, 2, 2, 2]
def baseStart_2487839 : Nat := 118140960795 + 2487839 * 2 ^ 59
def prefixEnd_2487839 : Nat := 4983230072969 + 3 ^ 40 * 2487839 * 2
def baseEnd_2487839 : Nat := 1277457198000997052171143

theorem tailTrace_2487839 : CollatzResearch.WordTrace tailWord_2487839 prefixEnd_2487839 1277457198000997052171143 := by
  unfold tailWord_2487839
  simp only [CollatzResearch.WordTrace]
  refine ⟨90738942833991666919162571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60492628555994444612775047 90738942833991666919162571)
  ·
    refine ⟨136108414250987500378743857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90738942833991666919162571 136108414250987500378743857)
    ·
      refine ⟨102081310688240625284057893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136108414250987500378743857 102081310688240625284057893)
      ·
        refine ⟨19140245754045117240760855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102081310688240625284057893 19140245754045117240760855)
        ·
          refine ⟨28710368631067675861141283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19140245754045117240760855 28710368631067675861141283)
          ·
            refine ⟨43065552946601513791711925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28710368631067675861141283 43065552946601513791711925)
            ·
              refine ⟨4037395588743891917972993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43065552946601513791711925 4037395588743891917972993)
              ·
                refine ⟨3028046691557918938479745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4037395588743891917972993 3028046691557918938479745)
                ·
                  refine ⟨2271035018668439203859809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3028046691557918938479745 2271035018668439203859809)
                  ·
                    refine ⟨1703276264001329402894857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2271035018668439203859809 1703276264001329402894857)
                    ·
                      refine ⟨1277457198000997052171143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1703276264001329402894857 1277457198000997052171143)
                      ·
                        rfl

theorem cell23_2487839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_2487839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487839 prefixEnd_2487839 := by exact prefixLift 2487839
  have htrace : WordTrace (prefixWord ++ tailWord_2487839) baseStart_2487839 baseEnd_2487839 := by
    simpa [prefixWord, tailWord_2487839, baseEnd_2487839] using wordTrace_append hprefix tailTrace_2487839
  have hstable : (prefixWord ++ tailWord_2487839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487839).length < 2 ^ (prefixWord ++ tailWord_2487839).sum := by decide
  have hdescent : baseEnd_2487839 < baseStart_2487839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487879 : List Nat := [1, 1, 4, 1, 5, 2, 1, 3, 5]
def baseStart_2487879 : Nat := 118140960795 + 2487879 * 2 ^ 59
def prefixEnd_2487879 : Nat := 4983230072969 + 3 ^ 40 * 2487879 * 2
def baseEnd_2487879 : Nat := 141941970803019655074551

theorem tailTrace_2487879 : CollatzResearch.WordTrace tailWord_2487879 prefixEnd_2487879 141941970803019655074551 := by
  unfold tailWord_2487879
  simp only [CollatzResearch.WordTrace]
  refine ⟨90740401753846753750618691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60493601169231169167079127 90740401753846753750618691)
  ·
    refine ⟨136110602630770130625928037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90740401753846753750618691 136110602630770130625928037)
    ·
      refine ⟨25520737993269399492361507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 136110602630770130625928037 25520737993269399492361507)
      ·
        refine ⟨38281106989904099238542261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25520737993269399492361507 38281106989904099238542261)
        ·
          refine ⟨3588853780303509303613337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38281106989904099238542261 3588853780303509303613337)
          ·
            refine ⟨2691640335227631977710003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3588853780303509303613337 2691640335227631977710003)
            ·
              refine ⟨4037460502841447966565005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2691640335227631977710003 4037460502841447966565005)
              ·
                refine ⟨1514047688565542987461877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4037460502841447966565005 1514047688565542987461877)
                ·
                  refine ⟨141941970803019655074551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1514047688565542987461877 141941970803019655074551)
                  ·
                    rfl

theorem cell23_2487879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 3, 5].length) (baseStart_2487879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487879 prefixEnd_2487879 := by exact prefixLift 2487879
  have htrace : WordTrace (prefixWord ++ tailWord_2487879) baseStart_2487879 baseEnd_2487879 := by
    simpa [prefixWord, tailWord_2487879, baseEnd_2487879] using wordTrace_append hprefix tailTrace_2487879
  have hstable : (prefixWord ++ tailWord_2487879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487879).length < 2 ^ (prefixWord ++ tailWord_2487879).sum := by decide
  have hdescent : baseEnd_2487879 < baseStart_2487879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487895 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 4]
def baseStart_2487895 : Nat := 118140960795 + 2487895 * 2 ^ 59
def prefixEnd_2487895 : Nat := 4983230072969 + 3 ^ 40 * 2487895 * 2
def baseEnd_2487895 : Nat := 1277485952917648833070885

theorem tailTrace_2487895 : CollatzResearch.WordTrace tailWord_2487895 prefixEnd_2487895 1277485952917648833070885 := by
  unfold tailWord_2487895
  simp only [CollatzResearch.WordTrace]
  refine ⟨90740985321788788483201139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60493990214525858988800759 90740985321788788483201139)
  ·
    refine ⟨136111477982683182724801709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90740985321788788483201139 136111477982683182724801709)
    ·
      refine ⟨51041804243506193521800641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136111477982683182724801709 51041804243506193521800641)
      ·
        refine ⟨38281353182629645141350481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51041804243506193521800641 38281353182629645141350481)
        ·
          refine ⟨28711014886972233856012861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38281353182629645141350481 28711014886972233856012861)
          ·
            refine ⟨10766630582614587696004823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28711014886972233856012861 10766630582614587696004823)
            ·
              refine ⟨16149945873921881544007235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10766630582614587696004823 16149945873921881544007235)
              ·
                refine ⟨24224918810882822316010853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16149945873921881544007235 24224918810882822316010853)
                ·
                  refine ⟨4542172277040529184252035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24224918810882822316010853 4542172277040529184252035)
                  ·
                    refine ⟨6813258415560793776378053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4542172277040529184252035 6813258415560793776378053)
                    ·
                      refine ⟨1277485952917648833070885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6813258415560793776378053 1277485952917648833070885)
                      ·
                        rfl

theorem cell23_2487895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_2487895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487895 prefixEnd_2487895 := by exact prefixLift 2487895
  have htrace : WordTrace (prefixWord ++ tailWord_2487895) baseStart_2487895 baseEnd_2487895 := by
    simpa [prefixWord, tailWord_2487895, baseEnd_2487895] using wordTrace_append hprefix tailTrace_2487895
  have hstable : (prefixWord ++ tailWord_2487895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487895).length < 2 ^ (prefixWord ++ tailWord_2487895).sum := by decide
  have hdescent : baseEnd_2487895 < baseStart_2487895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487928 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 2, 1, 9]
def baseStart_2487928 : Nat := 118140960795 + 2487928 * 2 ^ 59
def prefixEnd_2487928 : Nat := 4983230072969 + 3 ^ 40 * 2487928 * 2
def baseEnd_2487928 : Nat := 1277502897779247203958233

theorem tailTrace_2487928 : CollatzResearch.WordTrace tailWord_2487928 prefixEnd_2487928 1277502897779247203958233 := by
  unfold tailWord_2487928
  simp only [CollatzResearch.WordTrace]
  refine ⟨45371094465334617559576219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60494792620446156746101625 45371094465334617559576219)
  ·
    refine ⟨68056641698001926339364329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45371094465334617559576219 68056641698001926339364329)
    ·
      refine ⟨51042481273501444754523247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68056641698001926339364329 51042481273501444754523247)
      ·
        refine ⟨76563721910252167131784871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51042481273501444754523247 76563721910252167131784871)
        ·
          refine ⟨114845582865378250697677307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76563721910252167131784871 114845582865378250697677307)
          ·
            refine ⟨172268374298067376046515961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114845582865378250697677307 172268374298067376046515961)
            ·
              refine ⟨129201280723550532034886971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172268374298067376046515961 129201280723550532034886971)
              ·
                refine ⟨193801921085325798052330457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129201280723550532034886971 193801921085325798052330457)
                ·
                  refine ⟨145351440813994348539247843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193801921085325798052330457 145351440813994348539247843)
                  ·
                    refine ⟨218027161220991522808871765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 145351440813994348539247843 218027161220991522808871765)
                    ·
                      refine ⟨1277502897779247203958233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 218027161220991522808871765 1277502897779247203958233)
                      ·
                        rfl

theorem cell23_2487928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_2487928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487928 prefixEnd_2487928 := by exact prefixLift 2487928
  have htrace : WordTrace (prefixWord ++ tailWord_2487928) baseStart_2487928 baseEnd_2487928 := by
    simpa [prefixWord, tailWord_2487928, baseEnd_2487928] using wordTrace_append hprefix tailTrace_2487928
  have hstable : (prefixWord ++ tailWord_2487928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487928).length < 2 ^ (prefixWord ++ tailWord_2487928).sum := by decide
  have hdescent : baseEnd_2487928 < baseStart_2487928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2487996 : List Nat := [2, 2, 2, 3, 1, 2, 1, 5, 1, 1, 3]
def baseStart_2487996 : Nat := 118140960795 + 2487996 * 2 ^ 59
def prefixEnd_2487996 : Nat := 4983230072969 + 3 ^ 40 * 2487996 * 2
def baseEnd_2487996 : Nat := 1277537814463752937907921

theorem tailTrace_2487996 : CollatzResearch.WordTrace tailWord_2487996 prefixEnd_2487996 1277537814463752937907921 := by
  unfold tailWord_2487996
  simp only [CollatzResearch.WordTrace]
  refine ⟨45372334547211441366313921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60496446062948588488418561 45372334547211441366313921)
  ·
    refine ⟨34029250910408581024735441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45372334547211441366313921 34029250910408581024735441)
    ·
      refine ⟨25521938182806435768551581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34029250910408581024735441 25521938182806435768551581)
      ·
        refine ⟨9570726818552413413206843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25521938182806435768551581 9570726818552413413206843)
        ·
          refine ⟨14356090227828620119810265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9570726818552413413206843 14356090227828620119810265)
          ·
            refine ⟨10767067670871465089857699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14356090227828620119810265 10767067670871465089857699)
            ·
              refine ⟨16150601506307197634786549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10767067670871465089857699 16150601506307197634786549)
              ·
                refine ⟨1514118891216299778261239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16150601506307197634786549 1514118891216299778261239)
                ·
                  refine ⟨2271178336824449667391859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1514118891216299778261239 2271178336824449667391859)
                  ·
                    refine ⟨3406767505236674501087789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2271178336824449667391859 3406767505236674501087789)
                    ·
                      refine ⟨1277537814463752937907921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3406767505236674501087789 1277537814463752937907921)
                      ·
                        rfl

theorem cell23_2487996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_2487996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2487996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2487996 prefixEnd_2487996 := by exact prefixLift 2487996
  have htrace : WordTrace (prefixWord ++ tailWord_2487996) baseStart_2487996 baseEnd_2487996 := by
    simpa [prefixWord, tailWord_2487996, baseEnd_2487996] using wordTrace_append hprefix tailTrace_2487996
  have hstable : (prefixWord ++ tailWord_2487996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2487996).length < 2 ^ (prefixWord ++ tailWord_2487996).sum := by decide
  have hdescent : baseEnd_2487996 < baseStart_2487996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2487996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488013 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_2488013 : Nat := 118140960795 + 2488013 * 2 ^ 59
def prefixEnd_2488013 : Nat := 4983230072969 + 3 ^ 40 * 2488013 * 2
def baseEnd_2488013 : Nat := 1277546543634879371395343

theorem tailTrace_2488013 : CollatzResearch.WordTrace tailWord_2488013 prefixEnd_2488013 1277546543634879371395343 := by
  unfold tailWord_2488013
  simp only [CollatzResearch.WordTrace]
  refine ⟨90745289135361294635996693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60496859423574196423997795 90745289135361294635996693)
  ·
    refine ⟨4253685428220060686062345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 90745289135361294635996693 4253685428220060686062345)
    ·
      refine ⟨3190264071165045514546759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4253685428220060686062345 3190264071165045514546759)
      ·
        refine ⟨4785396106747568271820139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3190264071165045514546759 4785396106747568271820139)
        ·
          refine ⟨7178094160121352407730209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4785396106747568271820139 7178094160121352407730209)
          ·
            refine ⟨5383570620091014305797657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7178094160121352407730209 5383570620091014305797657)
            ·
              refine ⟨4037677965068260729348243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5383570620091014305797657 4037677965068260729348243)
              ·
                refine ⟨6056516947602391094022365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4037677965068260729348243 6056516947602391094022365)
                ·
                  refine ⟨2271193855350896660258387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6056516947602391094022365 2271193855350896660258387)
                  ·
                    refine ⟨3406790783026344990387581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2271193855350896660258387 3406790783026344990387581)
                    ·
                      refine ⟨1277546543634879371395343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3406790783026344990387581 1277546543634879371395343)
                      ·
                        rfl

theorem cell23_2488013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_2488013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488013 prefixEnd_2488013 := by exact prefixLift 2488013
  have htrace : WordTrace (prefixWord ++ tailWord_2488013) baseStart_2488013 baseEnd_2488013 := by
    simpa [prefixWord, tailWord_2488013, baseEnd_2488013] using wordTrace_append hprefix tailTrace_2488013
  have hstable : (prefixWord ++ tailWord_2488013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488013).length < 2 ^ (prefixWord ++ tailWord_2488013).sum := by decide
  have hdescent : baseEnd_2488013 < baseStart_2488013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488015 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 4]
def baseStart_2488015 : Nat := 118140960795 + 2488015 * 2 ^ 59
def prefixEnd_2488015 : Nat := 4983230072969 + 3 ^ 40 * 2488015 * 2
def baseEnd_2488015 : Nat := 1277547570596188363570333

theorem tailTrace_2488015 : CollatzResearch.WordTrace tailWord_2488015 prefixEnd_2488015 1277547570596188363570333 := by
  unfold tailWord_2488015
  simp only [CollatzResearch.WordTrace]
  refine ⟨90745362081354048977569499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60496908054236032651712999 90745362081354048977569499)
  ·
    refine ⟨136118043122031073466354249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90745362081354048977569499 136118043122031073466354249)
    ·
      refine ⟨102088532341523305099765687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136118043122031073466354249 102088532341523305099765687)
      ·
        refine ⟨153132798512284957649648531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102088532341523305099765687 153132798512284957649648531)
        ·
          refine ⟨229699197768427436474472797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153132798512284957649648531 229699197768427436474472797)
          ·
            refine ⟨86137199163160288677927299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229699197768427436474472797 86137199163160288677927299)
            ·
              refine ⟨129205798744740433016890949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86137199163160288677927299 129205798744740433016890949)
              ·
                refine ⟨24226087264638831190667053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129205798744740433016890949 24226087264638831190667053)
                ·
                  refine ⟨9084782724239561696500145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24226087264638831190667053 9084782724239561696500145)
                  ·
                    refine ⟨6813587043179671272375109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9084782724239561696500145 6813587043179671272375109)
                    ·
                      refine ⟨1277547570596188363570333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6813587043179671272375109 1277547570596188363570333)
                      ·
                        rfl

theorem cell23_2488015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_2488015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488015 prefixEnd_2488015 := by exact prefixLift 2488015
  have htrace : WordTrace (prefixWord ++ tailWord_2488015) baseStart_2488015 baseEnd_2488015 := by
    simpa [prefixWord, tailWord_2488015, baseEnd_2488015] using wordTrace_append hprefix tailTrace_2488015
  have hstable : (prefixWord ++ tailWord_2488015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488015).length < 2 ^ (prefixWord ++ tailWord_2488015).sum := by decide
  have hdescent : baseEnd_2488015 < baseStart_2488015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488032 : List Nat := [2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 4]
def baseStart_2488032 : Nat := 118140960795 + 2488032 * 2 ^ 59
def prefixEnd_2488032 : Nat := 4983230072969 + 3 ^ 40 * 2488032 * 2
def baseEnd_2488032 : Nat := 1277556299767314797057755

theorem tailTrace_2488032 : CollatzResearch.WordTrace tailWord_2488032 prefixEnd_2488032 1277556299767314797057755 := by
  unfold tailWord_2488032
  simp only [CollatzResearch.WordTrace]
  refine ⟨45372991061146230440469175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60497321414861640587292233 45372991061146230440469175)
  ·
    refine ⟨68059486591719345660703763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45372991061146230440469175 68059486591719345660703763)
    ·
      refine ⟨102089229887579018491055645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68059486591719345660703763 102089229887579018491055645)
      ·
        refine ⟨38283461207842131934145867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102089229887579018491055645 38283461207842131934145867)
        ·
          refine ⟨57425191811763197901218801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38283461207842131934145867 57425191811763197901218801)
          ·
            refine ⟨43068893858822398425914101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57425191811763197901218801 43068893858822398425914101)
            ·
              refine ⟨4037708799264599852429447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43068893858822398425914101 4037708799264599852429447)
              ·
                refine ⟨6056563198896899778644171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4037708799264599852429447 6056563198896899778644171)
                ·
                  refine ⟨9084844798345349667966257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6056563198896899778644171 9084844798345349667966257)
                  ·
                    refine ⟨6813633598759012250974693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9084844798345349667966257 6813633598759012250974693)
                    ·
                      refine ⟨1277556299767314797057755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6813633598759012250974693 1277556299767314797057755)
                      ·
                        rfl

theorem cell23_2488032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_2488032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488032 prefixEnd_2488032 := by exact prefixLift 2488032
  have htrace : WordTrace (prefixWord ++ tailWord_2488032) baseStart_2488032 baseEnd_2488032 := by
    simpa [prefixWord, tailWord_2488032, baseEnd_2488032] using wordTrace_append hprefix tailTrace_2488032
  have hstable : (prefixWord ++ tailWord_2488032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488032).length < 2 ^ (prefixWord ++ tailWord_2488032).sum := by decide
  have hdescent : baseEnd_2488032 < baseStart_2488032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488042 : List Nat := [3, 1, 3, 1, 1, 1, 6, 7]
def baseStart_2488042 : Nat := 118140960795 + 2488042 * 2 ^ 59
def prefixEnd_2488042 : Nat := 4983230072969 + 3 ^ 40 * 2488042 * 2
def baseEnd_2488042 : Nat := 47317090169402213256767

theorem tailTrace_2488042 : CollatzResearch.WordTrace tailWord_2488042 prefixEnd_2488042 47317090169402213256767 := by
  unfold tailWord_2488042
  simp only [CollatzResearch.WordTrace]
  refine ⟨22686586713064058147200595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60497564568170821725868253 22686586713064058147200595)
  ·
    refine ⟨34029880069596087220800893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22686586713064058147200595 34029880069596087220800893)
    ·
      refine ⟨12761205026098532707800335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34029880069596087220800893 12761205026098532707800335)
      ·
        refine ⟨19141807539147799061700503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12761205026098532707800335 19141807539147799061700503)
        ·
          refine ⟨28712711308721698592550755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19141807539147799061700503 28712711308721698592550755)
          ·
            refine ⟨43069066963082547888826133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28712711308721698592550755 43069066963082547888826133)
            ·
              refine ⟨2018862513894494432288725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43069066963082547888826133 2018862513894494432288725)
              ·
                refine ⟨47317090169402213256767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2018862513894494432288725 47317090169402213256767)
                ·
                  rfl

theorem cell23_2488042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 7].length) (baseStart_2488042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488042 prefixEnd_2488042 := by exact prefixLift 2488042
  have htrace : WordTrace (prefixWord ++ tailWord_2488042) baseStart_2488042 baseEnd_2488042 := by
    simpa [prefixWord, tailWord_2488042, baseEnd_2488042] using wordTrace_append hprefix tailTrace_2488042
  have hstable : (prefixWord ++ tailWord_2488042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488042).length < 2 ^ (prefixWord ++ tailWord_2488042).sum := by decide
  have hdescent : baseEnd_2488042 < baseStart_2488042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488113 : List Nat := [1, 2, 2, 3, 2, 3, 3, 1, 1, 3, 2]
def baseStart_2488113 : Nat := 118140960795 + 2488113 * 2 ^ 59
def prefixEnd_2488113 : Nat := 4983230072969 + 3 ^ 40 * 2488113 * 2
def baseEnd_2488113 : Nat := 1277597891700328980144883

theorem tailTrace_2488113 : CollatzResearch.WordTrace tailWord_2488113 prefixEnd_2488113 1277597891700328980144883 := by
  unfold tailWord_2488113
  simp only [CollatzResearch.WordTrace]
  refine ⟨90748936434999011714636993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60499290956666007809757995 90748936434999011714636993)
  ·
    refine ⟨68061702326249258785977745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90748936434999011714636993 68061702326249258785977745)
    ·
      refine ⟨51046276744686944089483309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68061702326249258785977745 51046276744686944089483309)
      ·
        refine ⟨19142353779257604033556241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51046276744686944089483309 19142353779257604033556241)
        ·
          refine ⟨14356765334443203025167181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19142353779257604033556241 14356765334443203025167181)
          ·
            refine ⟨5383787000416201134437693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14356765334443203025167181 5383787000416201134437693)
            ·
              refine ⟨2018920125156075425414135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5383787000416201134437693 2018920125156075425414135)
              ·
                refine ⟨3028380187734113138121203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018920125156075425414135 3028380187734113138121203)
                ·
                  refine ⟨4542570281601169707181805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3028380187734113138121203 4542570281601169707181805)
                  ·
                    refine ⟨1703463855600438640193177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4542570281601169707181805 1703463855600438640193177)
                    ·
                      refine ⟨1277597891700328980144883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1703463855600438640193177 1277597891700328980144883)
                      ·
                        rfl

theorem cell23_2488113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_2488113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488113 prefixEnd_2488113 := by exact prefixLift 2488113
  have htrace : WordTrace (prefixWord ++ tailWord_2488113) baseStart_2488113 baseEnd_2488113 := by
    simpa [prefixWord, tailWord_2488113, baseEnd_2488113] using wordTrace_append hprefix tailTrace_2488113
  have hstable : (prefixWord ++ tailWord_2488113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488113).length < 2 ^ (prefixWord ++ tailWord_2488113).sum := by decide
  have hdescent : baseEnd_2488113 < baseStart_2488113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488209 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 3, 4]
def baseStart_2488209 : Nat := 118140960795 + 2488209 * 2 ^ 59
def prefixEnd_2488209 : Nat := 4983230072969 + 3 ^ 40 * 2488209 * 2
def baseEnd_2488209 : Nat := 425882395281053534848147

theorem tailTrace_2488209 : CollatzResearch.WordTrace tailWord_2488209 prefixEnd_2488209 425882395281053534848147 := by
  unfold tailWord_2488209
  simp only [CollatzResearch.WordTrace]
  refine ⟨90752437842651220110131681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60501625228434146740087787 90752437842651220110131681)
  ·
    refine ⟨68064328381988415082598761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90752437842651220110131681 68064328381988415082598761)
    ·
      refine ⟨51048246286491311311949071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68064328381988415082598761 51048246286491311311949071)
      ·
        refine ⟨76572369429736966967923607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51048246286491311311949071 76572369429736966967923607)
        ·
          refine ⟨114858554144605450451885411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76572369429736966967923607 114858554144605450451885411)
          ·
            refine ⟨172287831216908175677828117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114858554144605450451885411 172287831216908175677828117)
            ·
              refine ⟨8075992088292570734898193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 172287831216908175677828117 8075992088292570734898193)
              ·
                refine ⟨6056994066219428051173645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8075992088292570734898193 6056994066219428051173645)
                ·
                  refine ⟨2271372774832285519190117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6056994066219428051173645 2271372774832285519190117)
                  ·
                    refine ⟨425882395281053534848147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2271372774832285519190117 425882395281053534848147)
                    ·
                      rfl

theorem cell23_2488209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_2488209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488209 prefixEnd_2488209 := by exact prefixLift 2488209
  have htrace : WordTrace (prefixWord ++ tailWord_2488209) baseStart_2488209 baseEnd_2488209 := by
    simpa [prefixWord, tailWord_2488209, baseEnd_2488209] using wordTrace_append hprefix tailTrace_2488209
  have hstable : (prefixWord ++ tailWord_2488209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488209).length < 2 ^ (prefixWord ++ tailWord_2488209).sum := by decide
  have hdescent : baseEnd_2488209 < baseStart_2488209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488242 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8]
def baseStart_2488242 : Nat := 118140960795 + 2488242 * 2 ^ 59
def prefixEnd_2488242 : Nat := 4983230072969 + 3 ^ 40 * 2488242 * 2
def baseEnd_2488242 : Nat := 1277664130704758975431789

theorem tailTrace_2488242 : CollatzResearch.WordTrace tailWord_2488242 prefixEnd_2488242 1277664130704758975431789 := by
  unfold tailWord_2488242
  simp only [CollatzResearch.WordTrace]
  refine ⟨22688410362882916686520745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60502427634354444497388653 22688410362882916686520745)
  ·
    refine ⟨17016307772162187514890559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22688410362882916686520745 17016307772162187514890559)
    ·
      refine ⟨25524461658243281272335839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17016307772162187514890559 25524461658243281272335839)
      ·
        refine ⟨38286692487364921908503759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25524461658243281272335839 38286692487364921908503759)
        ·
          refine ⟨57430038731047382862755639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38286692487364921908503759 57430038731047382862755639)
          ·
            refine ⟨86145058096571074294133459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57430038731047382862755639 86145058096571074294133459)
            ·
              refine ⟨129217587144856611441200189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86145058096571074294133459 129217587144856611441200189)
              ·
                refine ⟨48456595179321229290450071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129217587144856611441200189 48456595179321229290450071)
                ·
                  refine ⟨72684892768981843935675107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48456595179321229290450071 72684892768981843935675107)
                  ·
                    refine ⟨109027339153472765903512661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72684892768981843935675107 109027339153472765903512661)
                    ·
                      refine ⟨1277664130704758975431789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 109027339153472765903512661 1277664130704758975431789)
                      ·
                        rfl

theorem cell23_2488242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8].length) (baseStart_2488242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488242 prefixEnd_2488242 := by exact prefixLift 2488242
  have htrace : WordTrace (prefixWord ++ tailWord_2488242) baseStart_2488242 baseEnd_2488242 := by
    simpa [prefixWord, tailWord_2488242, baseEnd_2488242] using wordTrace_append hprefix tailTrace_2488242
  have hstable : (prefixWord ++ tailWord_2488242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488242).length < 2 ^ (prefixWord ++ tailWord_2488242).sum := by decide
  have hdescent : baseEnd_2488242 < baseStart_2488242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488243 : List Nat := [1, 1, 1, 2, 3, 1, 7, 2, 1, 4]
def baseStart_2488243 : Nat := 118140960795 + 2488243 * 2 ^ 59
def prefixEnd_2488243 : Nat := 4983230072969 + 3 ^ 40 * 2488243 * 2
def baseEnd_2488243 : Nat := 425888214728471157173095

theorem tailTrace_2488243 : CollatzResearch.WordTrace tailWord_2488243 prefixEnd_2488243 425888214728471157173095 := by
  unfold tailWord_2488243
  simp only [CollatzResearch.WordTrace]
  refine ⟨90753677924528043916869383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60502451949685362611246255 90753677924528043916869383)
  ·
    refine ⟨136130516886792065875304075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90753677924528043916869383 136130516886792065875304075)
    ·
      refine ⟨204195775330188098812956113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136130516886792065875304075 204195775330188098812956113)
      ·
        refine ⟨153146831497641074109717085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204195775330188098812956113 153146831497641074109717085)
        ·
          refine ⟨57430061811615402791143907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 153146831497641074109717085 57430061811615402791143907)
          ·
            refine ⟨86145092717423104186715861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57430061811615402791143907 86145092717423104186715861)
            ·
              refine ⟨2019025610564604004376153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 86145092717423104186715861 2019025610564604004376153)
              ·
                refine ⟨1514269207923453003282115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2019025610564604004376153 1514269207923453003282115)
                ·
                  refine ⟨2271403811885179504923173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1514269207923453003282115 2271403811885179504923173)
                  ·
                    refine ⟨425888214728471157173095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2271403811885179504923173 425888214728471157173095)
                    ·
                      rfl

theorem cell23_2488243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 2, 1, 4].length) (baseStart_2488243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488243 prefixEnd_2488243 := by exact prefixLift 2488243
  have htrace : WordTrace (prefixWord ++ tailWord_2488243) baseStart_2488243 baseEnd_2488243 := by
    simpa [prefixWord, tailWord_2488243, baseEnd_2488243] using wordTrace_append hprefix tailTrace_2488243
  have hstable : (prefixWord ++ tailWord_2488243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488243).length < 2 ^ (prefixWord ++ tailWord_2488243).sum := by decide
  have hdescent : baseEnd_2488243 < baseStart_2488243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488266 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 3, 1, 3]
def baseStart_2488266 : Nat := 118140960795 + 2488266 * 2 ^ 59
def prefixEnd_2488266 : Nat := 4983230072969 + 3 ^ 40 * 2488266 * 2
def baseEnd_2488266 : Nat := 1277676454240466881531679

theorem tailTrace_2488266 : CollatzResearch.WordTrace tailWord_2488266 prefixEnd_2488266 1277676454240466881531679 := by
  unfold tailWord_2488266
  simp only [CollatzResearch.WordTrace]
  refine ⟨22688629200861179711239163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60503011202296479229971101 22688629200861179711239163)
  ·
    refine ⟨34032943801291769566858745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22688629200861179711239163 34032943801291769566858745)
    ·
      refine ⟨25524707850968827175144059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34032943801291769566858745 25524707850968827175144059)
      ·
        refine ⟨38287061776453240762716089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25524707850968827175144059 38287061776453240762716089)
        ·
          refine ⟨28715296332339930572037067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38287061776453240762716089 28715296332339930572037067)
          ·
            refine ⟨43072944498509895858055601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28715296332339930572037067 43072944498509895858055601)
            ·
              refine ⟨32304708373882421893541701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43072944498509895858055601 32304708373882421893541701)
              ·
                refine ⟨6057132820102954105039069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32304708373882421893541701 6057132820102954105039069)
                ·
                  refine ⟨2271424807538607789389651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6057132820102954105039069 2271424807538607789389651)
                  ·
                    refine ⟨3407137211307911684084477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2271424807538607789389651 3407137211307911684084477)
                    ·
                      refine ⟨1277676454240466881531679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3407137211307911684084477 1277676454240466881531679)
                      ·
                        rfl

theorem cell23_2488266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_2488266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488266 prefixEnd_2488266 := by exact prefixLift 2488266
  have htrace : WordTrace (prefixWord ++ tailWord_2488266) baseStart_2488266 baseEnd_2488266 := by
    simpa [prefixWord, tailWord_2488266, baseEnd_2488266] using wordTrace_append hprefix tailTrace_2488266
  have hstable : (prefixWord ++ tailWord_2488266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488266).length < 2 ^ (prefixWord ++ tailWord_2488266).sum := by decide
  have hdescent : baseEnd_2488266 < baseStart_2488266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488299 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 4, 4]
def baseStart_2488299 : Nat := 118140960795 + 2488299 * 2 ^ 59
def prefixEnd_2488299 : Nat := 4983230072969 + 3 ^ 40 * 2488299 * 2
def baseEnd_2488299 : Nat := 425897799700688417473009

theorem tailTrace_2488299 : CollatzResearch.WordTrace tailWord_2488299 prefixEnd_2488299 425897799700688417473009 := by
  unfold tailWord_2488299
  simp only [CollatzResearch.WordTrace]
  refine ⟨90755720412325165480907951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60503813608216776987271967 90755720412325165480907951)
  ·
    refine ⟨136133580618487748221361927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90755720412325165480907951 136133580618487748221361927)
    ·
      refine ⟨204200370927731622332042891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136133580618487748221361927 204200370927731622332042891)
      ·
        refine ⟨306300556391597433498064337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204200370927731622332042891 306300556391597433498064337)
        ·
          refine ⟨229725417293698075123548253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306300556391597433498064337 229725417293698075123548253)
          ·
            refine ⟨86147031485136778171330595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229725417293698075123548253 86147031485136778171330595)
            ·
              refine ⟨129220547227705167256995893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86147031485136778171330595 129220547227705167256995893)
              ·
                refine ⟨12114426302597359430343365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129220547227705167256995893 12114426302597359430343365)
                ·
                  refine ⟨2271454931737004893189381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12114426302597359430343365 2271454931737004893189381)
                  ·
                    refine ⟨425897799700688417473009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2271454931737004893189381 425897799700688417473009)
                    ·
                      rfl

theorem cell23_2488299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 4].length) (baseStart_2488299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488299 prefixEnd_2488299 := by exact prefixLift 2488299
  have htrace : WordTrace (prefixWord ++ tailWord_2488299) baseStart_2488299 baseEnd_2488299 := by
    simpa [prefixWord, tailWord_2488299, baseEnd_2488299] using wordTrace_append hprefix tailTrace_2488299
  have hstable : (prefixWord ++ tailWord_2488299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488299).length < 2 ^ (prefixWord ++ tailWord_2488299).sum := by decide
  have hdescent : baseEnd_2488299 < baseStart_2488299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488316 : List Nat := [2, 2, 2, 1, 2, 2, 1, 5, 2, 4]
def baseStart_2488316 : Nat := 118140960795 + 2488316 * 2 ^ 59
def prefixEnd_2488316 : Nat := 4983230072969 + 3 ^ 40 * 2488316 * 2
def baseEnd_2488316 : Nat := 425900709424397228635483

theorem tailTrace_2488316 : CollatzResearch.WordTrace tailWord_2488316 prefixEnd_2488316 425900709424397228635483 := by
  unfold tailWord_2488316
  simp only [CollatzResearch.WordTrace]
  refine ⟨45378170226631788692138401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60504226968842384922851201 45378170226631788692138401)
  ·
    refine ⟨34033627669973841519103801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45378170226631788692138401 34033627669973841519103801)
    ·
      refine ⟨25525220752480381139327851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34033627669973841519103801 25525220752480381139327851)
      ·
        refine ⟨38287831128720571708991777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25525220752480381139327851 38287831128720571708991777)
        ·
          refine ⟨28715873346540428781743833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38287831128720571708991777 28715873346540428781743833)
          ·
            refine ⟨21536905009905321586307875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28715873346540428781743833 21536905009905321586307875)
            ·
              refine ⟨32305357514857982379461813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21536905009905321586307875 32305357514857982379461813)
              ·
                refine ⟨3028627267017935848074545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32305357514857982379461813 3028627267017935848074545)
                ·
                  refine ⟨2271470450263451886055909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3028627267017935848074545 2271470450263451886055909)
                  ·
                    refine ⟨425900709424397228635483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2271470450263451886055909 425900709424397228635483)
                    ·
                      rfl

theorem cell23_2488316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_2488316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488316 prefixEnd_2488316 := by exact prefixLift 2488316
  have htrace : WordTrace (prefixWord ++ tailWord_2488316) baseStart_2488316 baseEnd_2488316 := by
    simpa [prefixWord, tailWord_2488316, baseEnd_2488316] using wordTrace_append hprefix tailTrace_2488316
  have hstable : (prefixWord ++ tailWord_2488316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488316).length < 2 ^ (prefixWord ++ tailWord_2488316).sum := by decide
  have hdescent : baseEnd_2488316 < baseStart_2488316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488373 : List Nat := [1, 3, 3, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_2488373 : Nat := 118140960795 + 2488373 * 2 ^ 59
def prefixEnd_2488373 : Nat := 4983230072969 + 3 ^ 40 * 2488373 * 2
def baseEnd_2488373 : Nat := 1277731396670497962893687

theorem tailTrace_2488373 : CollatzResearch.WordTrace tailWord_2488373 prefixEnd_2488373 1277731396670497962893687 := by
  unfold tailWord_2488373
  simp only [CollatzResearch.WordTrace]
  refine ⟨90758419414057076119101773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60505612942704717412734515 90758419414057076119101773)
  ·
    refine ⟨34034407280271403544663165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90758419414057076119101773 34034407280271403544663165)
    ·
      refine ⟨12762902730101776329248687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34034407280271403544663165 12762902730101776329248687)
      ·
        refine ⟨19144354095152664493873031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12762902730101776329248687 19144354095152664493873031)
        ·
          refine ⟨28716531142728996740809547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19144354095152664493873031 28716531142728996740809547)
          ·
            refine ⟨43074796714093495111214321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28716531142728996740809547 43074796714093495111214321)
            ·
              refine ⟨32306097535570121333410741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43074796714093495111214321 32306097535570121333410741)
              ·
                refine ⟨3028696643959698875007257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32306097535570121333410741 3028696643959698875007257)
                ·
                  refine ⟨2271522482969774156255443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3028696643959698875007257 2271522482969774156255443)
                  ·
                    refine ⟨3407283724454661234383165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2271522482969774156255443 3407283724454661234383165)
                    ·
                      refine ⟨1277731396670497962893687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3407283724454661234383165 1277731396670497962893687)
                      ·
                        rfl

theorem cell23_2488373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_2488373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488373 prefixEnd_2488373 := by exact prefixLift 2488373
  have htrace : WordTrace (prefixWord ++ tailWord_2488373) baseStart_2488373 baseEnd_2488373 := by
    simpa [prefixWord, tailWord_2488373, baseEnd_2488373] using wordTrace_append hprefix tailTrace_2488373
  have hstable : (prefixWord ++ tailWord_2488373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488373).length < 2 ^ (prefixWord ++ tailWord_2488373).sum := by decide
  have hdescent : baseEnd_2488373 < baseStart_2488373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488383 : List Nat := [1, 1, 2, 2, 3, 1, 3, 4, 1, 3, 2]
def baseStart_2488383 : Nat := 118140960795 + 2488383 * 2 ^ 59
def prefixEnd_2488383 : Nat := 4983230072969 + 3 ^ 40 * 2488383 * 2
def baseEnd_2488383 : Nat := 1277736531477042923768641

theorem tailTrace_2488383 : CollatzResearch.WordTrace tailWord_2488383 prefixEnd_2488383 1277736531477042923768641 := by
  unfold tailWord_2488383
  simp only [CollatzResearch.WordTrace]
  refine ⟨90758784144020847826965803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60505856096013898551310535 90758784144020847826965803)
  ·
    refine ⟨136138176216031271740448705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90758784144020847826965803 136138176216031271740448705)
    ·
      refine ⟨102103632162023453805336529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136138176216031271740448705 102103632162023453805336529)
      ·
        refine ⟨76577724121517590354002397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102103632162023453805336529 76577724121517590354002397)
        ·
          refine ⟨28716646545569096382750899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76577724121517590354002397 28716646545569096382750899)
          ·
            refine ⟨43074969818353644574126349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28716646545569096382750899 43074969818353644574126349)
            ·
              refine ⟨16153113681882616715297381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43074969818353644574126349 16153113681882616715297381)
              ·
                refine ⟨3028708815352990634118259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16153113681882616715297381 3028708815352990634118259)
                ·
                  refine ⟨4543063223029485951177389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3028708815352990634118259 4543063223029485951177389)
                  ·
                    refine ⟨1703648708636057231691521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4543063223029485951177389 1703648708636057231691521)
                    ·
                      refine ⟨1277736531477042923768641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1703648708636057231691521 1277736531477042923768641)
                      ·
                        rfl

theorem cell23_2488383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 4, 1, 3, 2].length) (baseStart_2488383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488383 prefixEnd_2488383 := by exact prefixLift 2488383
  have htrace : WordTrace (prefixWord ++ tailWord_2488383) baseStart_2488383 baseEnd_2488383 := by
    simpa [prefixWord, tailWord_2488383, baseEnd_2488383] using wordTrace_append hprefix tailTrace_2488383
  have hstable : (prefixWord ++ tailWord_2488383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488383).length < 2 ^ (prefixWord ++ tailWord_2488383).sum := by decide
  have hdescent : baseEnd_2488383 < baseStart_2488383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488390 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_2488390 : Nat := 118140960795 + 2488390 * 2 ^ 59
def prefixEnd_2488390 : Nat := 4983230072969 + 3 ^ 40 * 2488390 * 2
def baseEnd_2488390 : Nat := 1277740125841624396381109

theorem tailTrace_2488390 : CollatzResearch.WordTrace tailWord_2488390 prefixEnd_2488390 1277740125841624396381109 := by
  unfold tailWord_2488390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2836219982968609000702207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60506026303330325348313749 2836219982968609000702207)
  ·
    refine ⟨4254329974452913501053311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2836219982968609000702207 4254329974452913501053311)
    ·
      refine ⟨6381494961679370251579967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4254329974452913501053311 6381494961679370251579967)
      ·
        refine ⟨9572242442519055377369951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6381494961679370251579967 9572242442519055377369951)
        ·
          refine ⟨14358363663778583066054927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9572242442519055377369951 14358363663778583066054927)
          ·
            refine ⟨21537545495667874599082391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14358363663778583066054927 21537545495667874599082391)
            ·
              refine ⟨32306318243501811898623587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21537545495667874599082391 32306318243501811898623587)
              ·
                refine ⟨48459477365252717847935381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32306318243501811898623587 48459477365252717847935381)
                ·
                  refine ⟨2271538001496221149121971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48459477365252717847935381 2271538001496221149121971)
                  ·
                    refine ⟨3407307002244331723682957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2271538001496221149121971 3407307002244331723682957)
                    ·
                      refine ⟨1277740125841624396381109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3407307002244331723682957 1277740125841624396381109)
                      ·
                        rfl

theorem cell23_2488390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_2488390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488390 prefixEnd_2488390 := by exact prefixLift 2488390
  have htrace : WordTrace (prefixWord ++ tailWord_2488390) baseStart_2488390 baseEnd_2488390 := by
    simpa [prefixWord, tailWord_2488390, baseEnd_2488390] using wordTrace_append hprefix tailTrace_2488390
  have hstable : (prefixWord ++ tailWord_2488390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488390).length < 2 ^ (prefixWord ++ tailWord_2488390).sum := by decide
  have hdescent : baseEnd_2488390 < baseStart_2488390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488399 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 5]
def baseStart_2488399 : Nat := 118140960795 + 2488399 * 2 ^ 59
def prefixEnd_2488399 : Nat := 4983230072969 + 3 ^ 40 * 2488399 * 2
def baseEnd_2488399 : Nat := 1277744747167514861168567

theorem tailTrace_2488399 : CollatzResearch.WordTrace tailWord_2488399 prefixEnd_2488399 1277744747167514861168567 := by
  unfold tailWord_2488399
  simp only [CollatzResearch.WordTrace]
  refine ⟨90759367711962882559548251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60506245141308588373032167 90759367711962882559548251)
  ·
    refine ⟨136139051567944323839322377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90759367711962882559548251 136139051567944323839322377)
    ·
      refine ⟨102104288675958242879491783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136139051567944323839322377 102104288675958242879491783)
      ·
        refine ⟨153156433013937364319237675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102104288675958242879491783 153156433013937364319237675)
        ·
          refine ⟨229734649520906046478856513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153156433013937364319237675 229734649520906046478856513)
          ·
            refine ⟨172300987140679534859142385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229734649520906046478856513 172300987140679534859142385)
            ·
              refine ⟨129225740355509651144356789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172300987140679534859142385 129225740355509651144356789)
              ·
                refine ⟨12114913158329029794783449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129225740355509651144356789 12114913158329029794783449)
                ·
                  refine ⟨9086184868746772346087587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12114913158329029794783449 9086184868746772346087587)
                  ·
                    refine ⟨13629277303120158519131381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9086184868746772346087587 13629277303120158519131381)
                    ·
                      refine ⟨1277744747167514861168567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13629277303120158519131381 1277744747167514861168567)
                      ·
                        rfl

theorem cell23_2488399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_2488399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488399 prefixEnd_2488399 := by exact prefixLift 2488399
  have htrace : WordTrace (prefixWord ++ tailWord_2488399) baseStart_2488399 baseEnd_2488399 := by
    simpa [prefixWord, tailWord_2488399, baseEnd_2488399] using wordTrace_append hprefix tailTrace_2488399
  have hstable : (prefixWord ++ tailWord_2488399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488399).length < 2 ^ (prefixWord ++ tailWord_2488399).sum := by decide
  have hdescent : baseEnd_2488399 < baseStart_2488399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488476 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 1, 2, 5]
def baseStart_2488476 : Nat := 118140960795 + 2488476 * 2 ^ 59
def prefixEnd_2488476 : Nat := 4983230072969 + 3 ^ 40 * 2488476 * 2
def baseEnd_2488476 : Nat := 1277784285177911059905713

theorem tailTrace_2488476 : CollatzResearch.WordTrace tailWord_2488476 prefixEnd_2488476 1277784285177911059905713 := by
  unfold tailWord_2488476
  simp only [CollatzResearch.WordTrace]
  refine ⟨45381088066341962355050641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60508117421789283140067521 45381088066341962355050641)
  ·
    refine ⟨34035816049756471766287981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45381088066341962355050641 34035816049756471766287981)
    ·
      refine ⟨12763431018658676912357993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34035816049756471766287981 12763431018658676912357993)
      ·
        refine ⟨9572573263994007684268495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12763431018658676912357993 9572573263994007684268495)
        ·
          refine ⟨14358859895991011526402743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9572573263994007684268495 14358859895991011526402743)
          ·
            refine ⟨21538289843986517289604115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14358859895991011526402743 21538289843986517289604115)
            ·
              refine ⟨32307434765979775934406173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21538289843986517289604115 32307434765979775934406173)
              ·
                refine ⟨12115288037242415975402315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32307434765979775934406173 12115288037242415975402315)
                ·
                  refine ⟨18172932055863623963103473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12115288037242415975402315 18172932055863623963103473)
                  ·
                    refine ⟨13629699041897717972327605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18172932055863623963103473 13629699041897717972327605)
                    ·
                      refine ⟨1277784285177911059905713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13629699041897717972327605 1277784285177911059905713)
                      ·
                        rfl

theorem cell23_2488476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_2488476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488476 prefixEnd_2488476 := by exact prefixLift 2488476
  have htrace : WordTrace (prefixWord ++ tailWord_2488476) baseStart_2488476 baseEnd_2488476 := by
    simpa [prefixWord, tailWord_2488476, baseEnd_2488476] using wordTrace_append hprefix tailTrace_2488476
  have hstable : (prefixWord ++ tailWord_2488476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488476).length < 2 ^ (prefixWord ++ tailWord_2488476).sum := by decide
  have hdescent : baseEnd_2488476 < baseStart_2488476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488503 : List Nat := [1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 4]
def baseStart_2488503 : Nat := 118140960795 + 2488503 * 2 ^ 59
def prefixEnd_2488503 : Nat := 4983230072969 + 3 ^ 40 * 2488503 * 2
def baseEnd_2488503 : Nat := 1277798149155582454268089

theorem tailTrace_2488503 : CollatzResearch.WordTrace tailWord_2488503 prefixEnd_2488503 1277798149155582454268089 := by
  unfold tailWord_2488503
  simp only [CollatzResearch.WordTrace]
  refine ⟨90763160903586108321334163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60508773935724072214222775 90763160903586108321334163)
  ·
    refine ⟨136144741355379162482001245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90763160903586108321334163 136144741355379162482001245)
    ·
      refine ⟨51054278008267185930750467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 136144741355379162482001245 51054278008267185930750467)
      ·
        refine ⟨76581417012400778896125701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51054278008267185930750467 76581417012400778896125701)
        ·
          refine ⟨14359015689825146043023569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76581417012400778896125701 14359015689825146043023569)
          ·
            refine ⟨10769261767368859532267677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14359015689825146043023569 10769261767368859532267677)
            ·
              refine ⟨4038473162763322324600379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10769261767368859532267677 4038473162763322324600379)
              ·
                refine ⟨6057709744144983486900569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4038473162763322324600379 6057709744144983486900569)
                ·
                  refine ⟨4543282308108737615175427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6057709744144983486900569 4543282308108737615175427)
                  ·
                    refine ⟨6814923462163106422763141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4543282308108737615175427 6814923462163106422763141)
                    ·
                      refine ⟨1277798149155582454268089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6814923462163106422763141 1277798149155582454268089)
                      ·
                        rfl

theorem cell23_2488503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_2488503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488503 prefixEnd_2488503 := by exact prefixLift 2488503
  have htrace : WordTrace (prefixWord ++ tailWord_2488503) baseStart_2488503 baseEnd_2488503 := by
    simpa [prefixWord, tailWord_2488503, baseEnd_2488503] using wordTrace_append hprefix tailTrace_2488503
  have hstable : (prefixWord ++ tailWord_2488503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488503).length < 2 ^ (prefixWord ++ tailWord_2488503).sum := by decide
  have hdescent : baseEnd_2488503 < baseStart_2488503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488530 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 3, 4]
def baseStart_2488530 : Nat := 118140960795 + 2488530 * 2 ^ 59
def prefixEnd_2488530 : Nat := 4983230072969 + 3 ^ 40 * 2488530 * 2
def baseEnd_2488530 : Nat := 425937337711084616210155

theorem tailTrace_2488530 : CollatzResearch.WordTrace tailWord_2488530 prefixEnd_2488530 425937337711084616210155 := by
  unfold tailWord_2488530
  simp only [CollatzResearch.WordTrace]
  refine ⟨22691036418622072983141761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60509430449658861288378029 22691036418622072983141761)
  ·
    refine ⟨17018277313966554737356321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22691036418622072983141761 17018277313966554737356321)
    ·
      refine ⟨12763707985474916053017241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17018277313966554737356321 12763707985474916053017241)
      ·
        refine ⟨9572780989106187039762931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12763707985474916053017241 9572780989106187039762931)
        ·
          refine ⟨14359171483659280559644397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9572780989106187039762931 14359171483659280559644397)
          ·
            refine ⟨5384689306372230209866649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14359171483659280559644397 5384689306372230209866649)
            ·
              refine ⟨4038516979779172657399987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5384689306372230209866649 4038516979779172657399987)
              ·
                refine ⟨6057775469668758986099981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4038516979779172657399987 6057775469668758986099981)
                ·
                  refine ⟨2271665801125784619787493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6057775469668758986099981 2271665801125784619787493)
                  ·
                    refine ⟨425937337711084616210155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2271665801125784619787493 425937337711084616210155)
                    ·
                      rfl

theorem cell23_2488530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_2488530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488530 prefixEnd_2488530 := by exact prefixLift 2488530
  have htrace : WordTrace (prefixWord ++ tailWord_2488530) baseStart_2488530 baseEnd_2488530 := by
    simpa [prefixWord, tailWord_2488530, baseEnd_2488530] using wordTrace_append hprefix tailTrace_2488530
  have hstable : (prefixWord ++ tailWord_2488530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488530).length < 2 ^ (prefixWord ++ tailWord_2488530).sum := by decide
  have hdescent : baseEnd_2488530 < baseStart_2488530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488563 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 1, 5, 2]
def baseStart_2488563 : Nat := 118140960795 + 2488563 * 2 ^ 59
def prefixEnd_2488563 : Nat := 4983230072969 + 3 ^ 40 * 2488563 * 2
def baseEnd_2488563 : Nat := 1277828957994852219517813

theorem tailTrace_2488563 : CollatzResearch.WordTrace tailWord_2488563 prefixEnd_2488563 1277828957994852219517813 := by
  unfold tailWord_2488563
  simp only [CollatzResearch.WordTrace]
  refine ⟨90765349283368738568518343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60510232855579159045678895 90765349283368738568518343)
  ·
    refine ⟨136148023925053107852777515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90765349283368738568518343 136148023925053107852777515)
    ·
      refine ⟨204222035887579661779166273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136148023925053107852777515 204222035887579661779166273)
      ·
        refine ⟨153166526915684746334374705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204222035887579661779166273 153166526915684746334374705)
        ·
          refine ⟨114874895186763559750781029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153166526915684746334374705 114874895186763559750781029)
          ·
            refine ⟨21539042847518167453271443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114874895186763559750781029 21539042847518167453271443)
            ·
              refine ⟨32308564271277251179907165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21539042847518167453271443 32308564271277251179907165)
              ·
                refine ⟨12115711601728969192465187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32308564271277251179907165 12115711601728969192465187)
                ·
                  refine ⟨18173567402593453788697781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12115711601728969192465187 18173567402593453788697781)
                  ·
                    refine ⟨1703771943993136292690417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18173567402593453788697781 1703771943993136292690417)
                    ·
                      refine ⟨1277828957994852219517813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1703771943993136292690417 1277828957994852219517813)
                      ·
                        rfl

theorem cell23_2488563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 5, 2].length) (baseStart_2488563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488563 prefixEnd_2488563 := by exact prefixLift 2488563
  have htrace : WordTrace (prefixWord ++ tailWord_2488563) baseStart_2488563 baseEnd_2488563 := by
    simpa [prefixWord, tailWord_2488563, baseEnd_2488563] using wordTrace_append hprefix tailTrace_2488563
  have hstable : (prefixWord ++ tailWord_2488563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488563).length < 2 ^ (prefixWord ++ tailWord_2488563).sum := by decide
  have hdescent : baseEnd_2488563 < baseStart_2488563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488610 : List Nat := [3, 3, 1, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_2488610 : Nat := 118140960795 + 2488610 * 2 ^ 59
def prefixEnd_2488610 : Nat := 4983230072969 + 3 ^ 40 * 2488610 * 2
def baseEnd_2488610 : Nat := 1277853091585613535630097

theorem tailTrace_2488610 : CollatzResearch.WordTrace tailWord_2488610 prefixEnd_2488610 1277853091585613535630097 := by
  unfold tailWord_2488610
  simp only [CollatzResearch.WordTrace]
  refine ⟨22691765878549616398869821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60511375676132310396986189 22691765878549616398869821)
  ·
    refine ⟨8509412204456106149576183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22691765878549616398869821 8509412204456106149576183)
    ·
      refine ⟨12764118306684159224364275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8509412204456106149576183 12764118306684159224364275)
      ·
        refine ⟨19146177460026238836546413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12764118306684159224364275 19146177460026238836546413)
        ·
          refine ⟨7179816547509839563704905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19146177460026238836546413 7179816547509839563704905)
          ·
            refine ⟨5384862410632379672778679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7179816547509839563704905 5384862410632379672778679)
            ·
              refine ⟨8077293615948569509168019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5384862410632379672778679 8077293615948569509168019)
              ·
                refine ⟨12115940423922854263752029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8077293615948569509168019 12115940423922854263752029)
                ·
                  refine ⟨4543477658971070348907011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12115940423922854263752029 4543477658971070348907011)
                  ·
                    refine ⟨6815216488456605523360517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4543477658971070348907011 6815216488456605523360517)
                    ·
                      refine ⟨1277853091585613535630097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6815216488456605523360517 1277853091585613535630097)
                      ·
                        rfl

theorem cell23_2488610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_2488610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488610 prefixEnd_2488610 := by exact prefixLift 2488610
  have htrace : WordTrace (prefixWord ++ tailWord_2488610) baseStart_2488610 baseEnd_2488610 := by
    simpa [prefixWord, tailWord_2488610, baseEnd_2488610] using wordTrace_append hprefix tailTrace_2488610
  have hstable : (prefixWord ++ tailWord_2488610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488610).length < 2 ^ (prefixWord ++ tailWord_2488610).sum := by decide
  have hdescent : baseEnd_2488610 < baseStart_2488610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488660 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 1, 3, 3]
def baseStart_2488660 : Nat := 118140960795 + 2488660 * 2 ^ 59
def prefixEnd_2488660 : Nat := 4983230072969 + 3 ^ 40 * 2488660 * 2
def baseEnd_2488660 : Nat := 1277878765618338340004867

theorem tailTrace_2488660 : CollatzResearch.WordTrace tailWord_2488660 prefixEnd_2488660 1277878765618338340004867 := by
  unfold tailWord_2488660
  simp only [CollatzResearch.WordTrace]
  refine ⟨45384443582008662067399717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60512591442678216089866289 45384443582008662067399717)
  ·
    refine ⟨8509583171626624137637447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45384443582008662067399717 8509583171626624137637447)
    ·
      refine ⟨12764374757439936206456171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8509583171626624137637447 12764374757439936206456171)
      ·
        refine ⟨19146562136159904309684257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12764374757439936206456171 19146562136159904309684257)
        ·
          refine ⟨14359921602119928232263193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19146562136159904309684257 14359921602119928232263193)
          ·
            refine ⟨10769941201589946174197395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14359921602119928232263193 10769941201589946174197395)
            ·
              refine ⟨16154911802384919261296093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10769941201589946174197395 16154911802384919261296093)
              ·
                refine ⟨6058091925894344722986035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16154911802384919261296093 6058091925894344722986035)
                ·
                  refine ⟨9087137888841517084479053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6058091925894344722986035 9087137888841517084479053)
                  ·
                    refine ⟨3407676708315568906679645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9087137888841517084479053 3407676708315568906679645)
                    ·
                      refine ⟨1277878765618338340004867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3407676708315568906679645 1277878765618338340004867)
                      ·
                        rfl

theorem cell23_2488660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_2488660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488660 prefixEnd_2488660 := by exact prefixLift 2488660
  have htrace : WordTrace (prefixWord ++ tailWord_2488660) baseStart_2488660 baseEnd_2488660 := by
    simpa [prefixWord, tailWord_2488660, baseEnd_2488660] using wordTrace_append hprefix tailTrace_2488660
  have hstable : (prefixWord ++ tailWord_2488660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488660).length < 2 ^ (prefixWord ++ tailWord_2488660).sum := by decide
  have hdescent : baseEnd_2488660 < baseStart_2488660 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488737 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 2, 1, 5]
def baseStart_2488737 : Nat := 118140960795 + 2488737 * 2 ^ 59
def prefixEnd_2488737 : Nat := 4983230072969 + 3 ^ 40 * 2488737 * 2
def baseEnd_2488737 : Nat := 1277918303628734538742013

theorem tailTrace_2488737 : CollatzResearch.WordTrace tailWord_2488737 prefixEnd_2488737 1277918303628734538742013 := by
  unfold tailWord_2488737
  simp only [CollatzResearch.WordTrace]
  refine ⟨90771695584738366285352465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60514463723158910856901643 90771695584738366285352465)
  ·
    refine ⟨68078771688553774714014349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90771695584738366285352465 68078771688553774714014349)
    ·
      refine ⟨25529539383207665517755381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68078771688553774714014349 25529539383207665517755381)
      ·
        refine ⟨2393394317175718642289567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25529539383207665517755381 2393394317175718642289567)
        ·
          refine ⟨3590091475763577963434351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393394317175718642289567 3590091475763577963434351)
          ·
            refine ⟨5385137213645366945151527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590091475763577963434351 5385137213645366945151527)
            ·
              refine ⟨8077705820468050417727291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5385137213645366945151527 8077705820468050417727291)
              ·
                refine ⟨12116558730702075626590937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8077705820468050417727291 12116558730702075626590937)
                ·
                  refine ⟨9087419048026556719943203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12116558730702075626590937 9087419048026556719943203)
                  ·
                    refine ⟨13631128572039835079914805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9087419048026556719943203 13631128572039835079914805)
                    ·
                      refine ⟨1277918303628734538742013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13631128572039835079914805 1277918303628734538742013)
                      ·
                        rfl

theorem cell23_2488737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_2488737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488737 prefixEnd_2488737 := by exact prefixLift 2488737
  have htrace : WordTrace (prefixWord ++ tailWord_2488737) baseStart_2488737 baseEnd_2488737 := by
    simpa [prefixWord, tailWord_2488737, baseEnd_2488737] using wordTrace_append hprefix tailTrace_2488737
  have hstable : (prefixWord ++ tailWord_2488737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488737).length < 2 ^ (prefixWord ++ tailWord_2488737).sum := by decide
  have hdescent : baseEnd_2488737 < baseStart_2488737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488757 : List Nat := [1, 3, 3, 2, 3, 2, 1, 1, 7]
def baseStart_2488757 : Nat := 118140960795 + 2488757 * 2 ^ 59
def prefixEnd_2488757 : Nat := 4983230072969 + 3 ^ 40 * 2488757 * 2
def baseEnd_2488757 : Nat := 141992063693536051165769

theorem tailTrace_2488757 : CollatzResearch.WordTrace tailWord_2488757 prefixEnd_2488757 141992063693536051165769 := by
  unfold tailWord_2488757
  simp only [CollatzResearch.WordTrace]
  refine ⟨90772425044665909701080525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60514950029777273134053683 90772425044665909701080525)
  ·
    refine ⟨34039659391749716137905197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90772425044665909701080525 34039659391749716137905197)
    ·
      refine ⟨12764872271906143551714449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34039659391749716137905197 12764872271906143551714449)
      ·
        refine ⟨9573654203929607663785837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12764872271906143551714449 9573654203929607663785837)
        ·
          refine ⟨3590120326473602873919689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9573654203929607663785837 3590120326473602873919689)
          ·
            refine ⟨2692590244855202155439767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3590120326473602873919689 2692590244855202155439767)
            ·
              refine ⟨4038885367282803233159651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2692590244855202155439767 4038885367282803233159651)
              ·
                refine ⟨6058328050924204849739477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4038885367282803233159651 6058328050924204849739477)
                ·
                  refine ⟨141992063693536051165769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6058328050924204849739477 141992063693536051165769)
                  ·
                    rfl

theorem cell23_2488757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 7].length) (baseStart_2488757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488757 prefixEnd_2488757 := by exact prefixLift 2488757
  have htrace : WordTrace (prefixWord ++ tailWord_2488757) baseStart_2488757 baseEnd_2488757 := by
    simpa [prefixWord, tailWord_2488757, baseEnd_2488757] using wordTrace_append hprefix tailTrace_2488757
  have hstable : (prefixWord ++ tailWord_2488757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488757).length < 2 ^ (prefixWord ++ tailWord_2488757).sum := by decide
  have hdescent : baseEnd_2488757 < baseStart_2488757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488760 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 2, 5, 2]
def baseStart_2488760 : Nat := 118140960795 + 2488760 * 2 ^ 59
def prefixEnd_2488760 : Nat := 4983230072969 + 3 ^ 40 * 2488760 * 2
def baseEnd_2488760 : Nat := 1277930113683787948754407

theorem tailTrace_2488760 : CollatzResearch.WordTrace tailWord_2488760 prefixEnd_2488760 1277930113683787948754407 := by
  unfold tailWord_2488760
  simp only [CollatzResearch.WordTrace]
  refine ⟨45386267231827520606719867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60515022975770027475626489 45386267231827520606719867)
  ·
    refine ⟨68079400847741280910079801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45386267231827520606719867 68079400847741280910079801)
    ·
      refine ⟨51059550635805960682559851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68079400847741280910079801 51059550635805960682559851)
      ·
        refine ⟨76589325953708941023839777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51059550635805960682559851 76589325953708941023839777)
        ·
          refine ⟨57441994465281705767879833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76589325953708941023839777 57441994465281705767879833)
          ·
            refine ⟨43081495848961279325909875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57441994465281705767879833 43081495848961279325909875)
            ·
              refine ⟨64622243773441918988864813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43081495848961279325909875 64622243773441918988864813)
              ·
                refine ⟨24233341415040719620824305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64622243773441918988864813 24233341415040719620824305)
                ·
                  refine ⟨18175006061280539715618229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24233341415040719620824305 18175006061280539715618229)
                  ·
                    refine ⟨1703906818245050598339209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18175006061280539715618229 1703906818245050598339209)
                    ·
                      refine ⟨1277930113683787948754407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1703906818245050598339209 1277930113683787948754407)
                      ·
                        rfl

theorem cell23_2488760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2, 5, 2].length) (baseStart_2488760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488760 prefixEnd_2488760 := by exact prefixLift 2488760
  have htrace : WordTrace (prefixWord ++ tailWord_2488760) baseStart_2488760 baseEnd_2488760 := by
    simpa [prefixWord, tailWord_2488760, baseEnd_2488760] using wordTrace_append hprefix tailTrace_2488760
  have hstable : (prefixWord ++ tailWord_2488760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488760).length < 2 ^ (prefixWord ++ tailWord_2488760).sum := by decide
  have hdescent : baseEnd_2488760 < baseStart_2488760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488807 : List Nat := [1, 1, 5, 2, 1, 1, 2, 2, 2, 4, 2]
def baseStart_2488807 : Nat := 118140960795 + 2488807 * 2 ^ 59
def prefixEnd_2488807 : Nat := 4983230072969 + 3 ^ 40 * 2488807 * 2
def baseEnd_2488807 : Nat := 1277954247274549264866691

theorem tailTrace_2488807 : CollatzResearch.WordTrace tailWord_2488807 prefixEnd_2488807 1277954247274549264866691 := by
  unfold tailWord_2488807
  simp only [CollatzResearch.WordTrace]
  refine ⟨90774248694484768240400675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60516165796323178826933783 90774248694484768240400675)
  ·
    refine ⟨136161373041727152360601013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90774248694484768240400675 136161373041727152360601013)
    ·
      refine ⟨12765128722661920533806345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 136161373041727152360601013 12765128722661920533806345)
      ·
        refine ⟨9573846541996440400354759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12765128722661920533806345 9573846541996440400354759)
        ·
          refine ⟨14360769812994660600532139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9573846541996440400354759 14360769812994660600532139)
          ·
            refine ⟨21541154719491990900798209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14360769812994660600532139 21541154719491990900798209)
            ·
              refine ⟨16155866039618993175598657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21541154719491990900798209 16155866039618993175598657)
              ·
                refine ⟨12116899529714244881698993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16155866039618993175598657 12116899529714244881698993)
                ·
                  refine ⟨9087674647285683661274245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12116899529714244881698993 9087674647285683661274245)
                  ·
                    refine ⟨1703938996366065686488921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9087674647285683661274245 1703938996366065686488921)
                    ·
                      refine ⟨1277954247274549264866691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1703938996366065686488921 1277954247274549264866691)
                      ·
                        rfl

theorem cell23_2488807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_2488807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488807 prefixEnd_2488807 := by exact prefixLift 2488807
  have htrace : WordTrace (prefixWord ++ tailWord_2488807) baseStart_2488807 baseEnd_2488807 := by
    simpa [prefixWord, tailWord_2488807, baseEnd_2488807] using wordTrace_append hprefix tailTrace_2488807
  have hstable : (prefixWord ++ tailWord_2488807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488807).length < 2 ^ (prefixWord ++ tailWord_2488807).sum := by decide
  have hdescent : baseEnd_2488807 < baseStart_2488807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488838 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2488838 : Nat := 118140960795 + 2488838 * 2 ^ 59
def prefixEnd_2488838 : Nat := 4983230072969 + 3 ^ 40 * 2488838 * 2
def baseEnd_2488838 : Nat := 425990055058279547859683

theorem tailTrace_2488838 : CollatzResearch.WordTrace tailWord_2488838 prefixEnd_2488838 425990055058279547859683 := by
  unfold tailWord_2488838
  simp only [CollatzResearch.WordTrace]
  refine ⟨2836730604917889391711849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60516919571581640356519445 2836730604917889391711849)
  ·
    refine ⟨2127547953688417043783887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2836730604917889391711849 2127547953688417043783887)
    ·
      refine ⟨3191321930532625565675831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2127547953688417043783887 3191321930532625565675831)
      ·
        refine ⟨4786982895798938348513747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3191321930532625565675831 4786982895798938348513747)
        ·
          refine ⟨7180474343698407522770621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4786982895798938348513747 7180474343698407522770621)
          ·
            refine ⟨2692677878886902821038983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7180474343698407522770621 2692677878886902821038983)
            ·
              refine ⟨4039016818330354231558475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2692677878886902821038983 4039016818330354231558475)
              ·
                refine ⟨6058525227495531347337713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4039016818330354231558475 6058525227495531347337713)
                ·
                  refine ⟨4543893920621648510503285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6058525227495531347337713 4543893920621648510503285)
                  ·
                    refine ⟨425990055058279547859683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4543893920621648510503285 425990055058279547859683)
                    ·
                      rfl

theorem cell23_2488838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2488838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488838 prefixEnd_2488838 := by exact prefixLift 2488838
  have htrace : WordTrace (prefixWord ++ tailWord_2488838) baseStart_2488838 baseEnd_2488838 := by
    simpa [prefixWord, tailWord_2488838, baseEnd_2488838] using wordTrace_append hprefix tailTrace_2488838
  have hstable : (prefixWord ++ tailWord_2488838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488838).length < 2 ^ (prefixWord ++ tailWord_2488838).sum := by decide
  have hdescent : baseEnd_2488838 < baseStart_2488838 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488844 : List Nat := [2, 2, 1, 2, 4, 3, 1, 1, 2, 2, 3]
def baseStart_2488844 : Nat := 118140960795 + 2488844 * 2 ^ 59
def prefixEnd_2488844 : Nat := 4983230072969 + 3 ^ 40 * 2488844 * 2
def baseEnd_2488844 : Nat := 1277973246058765620104021

theorem tailTrace_2488844 : CollatzResearch.WordTrace tailWord_2488844 prefixEnd_2488844 1277973246058765620104021 := by
  unfold tailWord_2488844
  simp only [CollatzResearch.WordTrace]
  refine ⟨45387799097675361779748793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60517065463567149039665057 45387799097675361779748793)
  ·
    refine ⟨34040849323256521334811595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45387799097675361779748793 34040849323256521334811595)
    ·
      refine ⟨51061273984884782002217393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34040849323256521334811595 51061273984884782002217393)
      ·
        refine ⟨38295955488663586501663045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51061273984884782002217393 38295955488663586501663045)
        ·
          refine ⟨7180491654124422469061821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38295955488663586501663045 7180491654124422469061821)
          ·
            refine ⟨2692684370296658425898183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7180491654124422469061821 2692684370296658425898183)
            ·
              refine ⟨4039026555444987638847275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2692684370296658425898183 4039026555444987638847275)
              ·
                refine ⟨6058539833167481458270913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4039026555444987638847275 6058539833167481458270913)
                ·
                  refine ⟨4543904874875611093703185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6058539833167481458270913 4543904874875611093703185)
                  ·
                    refine ⟨3407928656156708320277389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4543904874875611093703185 3407928656156708320277389)
                    ·
                      refine ⟨1277973246058765620104021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3407928656156708320277389 1277973246058765620104021)
                      ·
                        rfl

theorem cell23_2488844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_2488844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488844 prefixEnd_2488844 := by exact prefixLift 2488844
  have htrace : WordTrace (prefixWord ++ tailWord_2488844) baseStart_2488844 baseEnd_2488844 := by
    simpa [prefixWord, tailWord_2488844, baseEnd_2488844] using wordTrace_append hprefix tailTrace_2488844
  have hstable : (prefixWord ++ tailWord_2488844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488844).length < 2 ^ (prefixWord ++ tailWord_2488844).sum := by decide
  have hdescent : baseEnd_2488844 < baseStart_2488844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488864 : List Nat := [2, 1, 1, 6, 2, 2, 1, 2, 6]
def baseStart_2488864 : Nat := 118140960795 + 2488864 * 2 ^ 59
def prefixEnd_2488864 : Nat := 4983230072969 + 3 ^ 40 * 2488864 * 2
def baseEnd_2488864 : Nat := 141998168407983949094881

theorem tailTrace_2488864 : CollatzResearch.WordTrace tailWord_2488864 prefixEnd_2488864 141998168407983949094881 := by
  unfold tailWord_2488864
  simp only [CollatzResearch.WordTrace]
  refine ⟨45388163827639133487612823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60517551770185511316817097 45388163827639133487612823)
  ·
    refine ⟨68082245741458700231419235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45388163827639133487612823 68082245741458700231419235)
    ·
      refine ⟨102123368612188050347128853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68082245741458700231419235 102123368612188050347128853)
      ·
        refine ⟨4787032903696314860021665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102123368612188050347128853 4787032903696314860021665)
        ·
          refine ⟨3590274677772236145016249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4787032903696314860021665 3590274677772236145016249)
          ·
            refine ⟨2692706008329177108762187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3590274677772236145016249 2692706008329177108762187)
            ·
              refine ⟨4039059012493765663143281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2692706008329177108762187 4039059012493765663143281)
              ·
                refine ⟨3029294259370324247357461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039059012493765663143281 3029294259370324247357461)
                ·
                  refine ⟨141998168407983949094881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3029294259370324247357461 141998168407983949094881)
                  ·
                    rfl

theorem cell23_2488864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 2, 6].length) (baseStart_2488864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488864 prefixEnd_2488864 := by exact prefixLift 2488864
  have htrace : WordTrace (prefixWord ++ tailWord_2488864) baseStart_2488864 baseEnd_2488864 := by
    simpa [prefixWord, tailWord_2488864, baseEnd_2488864] using wordTrace_append hprefix tailTrace_2488864
  have hstable : (prefixWord ++ tailWord_2488864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488864).length < 2 ^ (prefixWord ++ tailWord_2488864).sum := by decide
  have hdescent : baseEnd_2488864 < baseStart_2488864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488874 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_2488874 : Nat := 118140960795 + 2488874 * 2 ^ 59
def prefixEnd_2488874 : Nat := 4983230072969 + 3 ^ 40 * 2488874 * 2
def baseEnd_2488874 : Nat := 1277988650478400502728883

theorem tailTrace_2488874 : CollatzResearch.WordTrace tailWord_2488874 prefixEnd_2488874 1277988650478400502728883 := by
  unfold tailWord_2488874
  simp only [CollatzResearch.WordTrace]
  refine ⟨22694173096310509670772419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60517794923494692455393117 22694173096310509670772419)
  ·
    refine ⟨34041259644465764506158629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22694173096310509670772419 34041259644465764506158629)
    ·
      refine ⟨6382736183337330844904743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34041259644465764506158629 6382736183337330844904743)
      ·
        refine ⟨9574104275005996267357115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6382736183337330844904743 9574104275005996267357115)
        ·
          refine ⟨14361156412508994401035673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9574104275005996267357115 14361156412508994401035673)
          ·
            refine ⟨10770867309381745800776755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14361156412508994401035673 10770867309381745800776755)
            ·
              refine ⟨16156300964072618701165133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10770867309381745800776755 16156300964072618701165133)
              ·
                refine ⟨6058612861527232012936925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16156300964072618701165133 6058612861527232012936925)
                ·
                  refine ⟨2271979823072712004851347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6058612861527232012936925 2271979823072712004851347)
                  ·
                    refine ⟨3407969734609068007277021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2271979823072712004851347 3407969734609068007277021)
                    ·
                      refine ⟨1277988650478400502728883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3407969734609068007277021 1277988650478400502728883)
                      ·
                        rfl

theorem cell23_2488874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_2488874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488874 prefixEnd_2488874 := by exact prefixLift 2488874
  have htrace : WordTrace (prefixWord ++ tailWord_2488874) baseStart_2488874 baseEnd_2488874 := by
    simpa [prefixWord, tailWord_2488874, baseEnd_2488874] using wordTrace_append hprefix tailTrace_2488874
  have hstable : (prefixWord ++ tailWord_2488874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488874).length < 2 ^ (prefixWord ++ tailWord_2488874).sum := by decide
  have hdescent : baseEnd_2488874 < baseStart_2488874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488880 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 4]
def baseStart_2488880 : Nat := 118140960795 + 2488880 * 2 ^ 59
def prefixEnd_2488880 : Nat := 4983230072969 + 3 ^ 40 * 2488880 * 2
def baseEnd_2488880 : Nat := 1277991731362327479253855

theorem tailTrace_2488880 : CollatzResearch.WordTrace tailWord_2488880 prefixEnd_2488880 1277991731362327479253855 := by
  unfold tailWord_2488880
  simp only [CollatzResearch.WordTrace]
  refine ⟨45388455611610150853904047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60517940815480201138538729 45388455611610150853904047)
  ·
    refine ⟨68082683417415226280856071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45388455611610150853904047 68082683417415226280856071)
    ·
      refine ⟨102124025126122839421284107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68082683417415226280856071 102124025126122839421284107)
      ·
        refine ⟨153186037689184259131926161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102124025126122839421284107 153186037689184259131926161)
        ·
          refine ⟨114889528266888194348944621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153186037689184259131926161 114889528266888194348944621)
          ·
            refine ⟨43083573100083072880854233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114889528266888194348944621 43083573100083072880854233)
            ·
              refine ⟨32312679825062304660640675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43083573100083072880854233 32312679825062304660640675)
              ·
                refine ⟨48469019737593456990961013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32312679825062304660640675 48469019737593456990961013)
                ·
                  refine ⟨4543970600399386592902595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48469019737593456990961013 4543970600399386592902595)
                  ·
                    refine ⟨6815955900599079889353893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4543970600399386592902595 6815955900599079889353893)
                    ·
                      refine ⟨1277991731362327479253855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6815955900599079889353893 1277991731362327479253855)
                      ·
                        rfl

theorem cell23_2488880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 4].length) (baseStart_2488880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488880 prefixEnd_2488880 := by exact prefixLift 2488880
  have htrace : WordTrace (prefixWord ++ tailWord_2488880) baseStart_2488880 baseEnd_2488880 := by
    simpa [prefixWord, tailWord_2488880, baseEnd_2488880] using wordTrace_append hprefix tailTrace_2488880
  have hstable : (prefixWord ++ tailWord_2488880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488880).length < 2 ^ (prefixWord ++ tailWord_2488880).sum := by decide
  have hdescent : baseEnd_2488880 < baseStart_2488880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488941 : List Nat := [1, 5, 1, 1, 3, 1, 4, 1, 2, 4]
def baseStart_2488941 : Nat := 118140960795 + 2488941 * 2 ^ 59
def prefixEnd_2488941 : Nat := 4983230072969 + 3 ^ 40 * 2488941 * 2
def baseEnd_2488941 : Nat := 426007684560750580197025

theorem tailTrace_2488941 : CollatzResearch.WordTrace tailWord_2488941 prefixEnd_2488941 426007684560750580197025 := by
  unfold tailWord_2488941
  simp only [CollatzResearch.WordTrace]
  refine ⟨90779136075999309125778677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60519424050666206083852451 90779136075999309125778677)
  ·
    refine ⟨8510544007124935230541751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90779136075999309125778677 8510544007124935230541751)
    ·
      refine ⟨12765816010687402845812627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8510544007124935230541751 12765816010687402845812627)
      ·
        refine ⟨19148724016031104268718941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12765816010687402845812627 19148724016031104268718941)
        ·
          refine ⟨7180771506011664100769603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19148724016031104268718941 7180771506011664100769603)
          ·
            refine ⟨10771157259017496151154405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7180771506011664100769603 10771157259017496151154405)
            ·
              refine ⟨2019591986065780528341451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10771157259017496151154405 2019591986065780528341451)
              ·
                refine ⟨3029387979098670792512177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2019591986065780528341451 3029387979098670792512177)
                ·
                  refine ⟨2272040984324003094384133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3029387979098670792512177 2272040984324003094384133)
                  ·
                    refine ⟨426007684560750580197025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2272040984324003094384133 426007684560750580197025)
                    ·
                      rfl

theorem cell23_2488941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_2488941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488941 prefixEnd_2488941 := by exact prefixLift 2488941
  have htrace : WordTrace (prefixWord ++ tailWord_2488941) baseStart_2488941 baseEnd_2488941 := by
    simpa [prefixWord, tailWord_2488941, baseEnd_2488941] using wordTrace_append hprefix tailTrace_2488941
  have hstable : (prefixWord ++ tailWord_2488941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488941).length < 2 ^ (prefixWord ++ tailWord_2488941).sum := by decide
  have hdescent : baseEnd_2488941 < baseStart_2488941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488947 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 6, 1, 3]
def baseStart_2488947 : Nat := 118140960795 + 2488947 * 2 ^ 59
def prefixEnd_2488947 : Nat := 4983230072969 + 3 ^ 40 * 2488947 * 2
def baseEnd_2488947 : Nat := 1278026134566178717116047

theorem tailTrace_2488947 : CollatzResearch.WordTrace tailWord_2488947 prefixEnd_2488947 1278026134566178717116047 := by
  unfold tailWord_2488947
  simp only [CollatzResearch.WordTrace]
  refine ⟨90779354913977572150497095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60519569942651714766998063 90779354913977572150497095)
  ·
    refine ⟨136169032370966358225745643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90779354913977572150497095 136169032370966358225745643)
    ·
      refine ⟨204253548556449537338618465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136169032370966358225745643 204253548556449537338618465)
      ·
        refine ⟨153190161417337153003963849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204253548556449537338618465 153190161417337153003963849)
        ·
          refine ⟨114892621063002864752972887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153190161417337153003963849 114892621063002864752972887)
          ·
            refine ⟨172338931594504297129459331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114892621063002864752972887 172338931594504297129459331)
            ·
              refine ⟨258508397391756445694188997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172338931594504297129459331 258508397391756445694188997)
              ·
                refine ⟨48470324510954333567660437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 258508397391756445694188997 48470324510954333567660437)
                ·
                  refine ⟨2272046461450984385984083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48470324510954333567660437 2272046461450984385984083)
                  ·
                    refine ⟨3408069692176476578976125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2272046461450984385984083 3408069692176476578976125)
                    ·
                      refine ⟨1278026134566178717116047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3408069692176476578976125 1278026134566178717116047)
                      ·
                        rfl

theorem cell23_2488947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 1, 3].length) (baseStart_2488947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488947 prefixEnd_2488947 := by exact prefixLift 2488947
  have htrace : WordTrace (prefixWord ++ tailWord_2488947) baseStart_2488947 baseEnd_2488947 := by
    simpa [prefixWord, tailWord_2488947, baseEnd_2488947] using wordTrace_append hprefix tailTrace_2488947
  have hstable : (prefixWord ++ tailWord_2488947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488947).length < 2 ^ (prefixWord ++ tailWord_2488947).sum := by decide
  have hdescent : baseEnd_2488947 < baseStart_2488947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2488964 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_2488964 : Nat := 118140960795 + 2488964 * 2 ^ 59
def prefixEnd_2488964 : Nat := 4983230072969 + 3 ^ 40 * 2488964 * 2
def baseEnd_2488964 : Nat := 1278034863737305150603469

theorem tailTrace_2488964 : CollatzResearch.WordTrace tailWord_2488964 prefixEnd_2488964 1278034863737305150603469 := by
  unfold tailWord_2488964
  simp only [CollatzResearch.WordTrace]
  refine ⟨45389987477457992026932973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60519983303277322702577297 45389987477457992026932973)
  ·
    refine ⟨17021245304046747010099865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45389987477457992026932973 17021245304046747010099865)
    ·
      refine ⟨12765933978035060257574899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17021245304046747010099865 12765933978035060257574899)
      ·
        refine ⟨19148900967052590386362349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12765933978035060257574899 19148900967052590386362349)
        ·
          refine ⟨7180837862644721394885881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19148900967052590386362349 7180837862644721394885881)
          ·
            refine ⟨5385628396983541046164411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7180837862644721394885881 5385628396983541046164411)
            ·
              refine ⟨8078442595475311569246617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5385628396983541046164411 8078442595475311569246617)
              ·
                refine ⟨6058831946606483676934963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8078442595475311569246617 6058831946606483676934963)
                ·
                  refine ⟨9088247919909725515402445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6058831946606483676934963 9088247919909725515402445)
                  ·
                    refine ⟨3408092969966147068275917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9088247919909725515402445 3408092969966147068275917)
                    ·
                      refine ⟨1278034863737305150603469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3408092969966147068275917 1278034863737305150603469)
                      ·
                        rfl

theorem cell23_2488964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_2488964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2488964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2488964 prefixEnd_2488964 := by exact prefixLift 2488964
  have htrace : WordTrace (prefixWord ++ tailWord_2488964) baseStart_2488964 baseEnd_2488964 := by
    simpa [prefixWord, tailWord_2488964, baseEnd_2488964] using wordTrace_append hprefix tailTrace_2488964
  have hstable : (prefixWord ++ tailWord_2488964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2488964).length < 2 ^ (prefixWord ++ tailWord_2488964).sum := by decide
  have hdescent : baseEnd_2488964 < baseStart_2488964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2488964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489025 : List Nat := [1, 2, 6, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_2489025 : Nat := 118140960795 + 2489025 * 2 ^ 59
def prefixEnd_2489025 : Nat := 4983230072969 + 3 ^ 40 * 2489025 * 2
def baseEnd_2489025 : Nat := 1278066186057229411940689

theorem tailTrace_2489025 : CollatzResearch.WordTrace tailWord_2489025 prefixEnd_2489025 1278066186057229411940689 := by
  unfold tailWord_2489025
  simp only [CollatzResearch.WordTrace]
  refine ⟨90782199807694991471836529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60521466538463327647891019 90782199807694991471836529)
  ·
    refine ⟨68086649855771243603877397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90782199807694991471836529 68086649855771243603877397)
    ·
      refine ⟨3191561711989277043931753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68086649855771243603877397 3191561711989277043931753)
      ·
        refine ⟨2393671283991957782948815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3191561711989277043931753 2393671283991957782948815)
        ·
          refine ⟨3590506925987936674423223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393671283991957782948815 3590506925987936674423223)
          ·
            refine ⟨5385760388981905011634835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590506925987936674423223 5385760388981905011634835)
            ·
              refine ⟨8078640583472857517452253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5385760388981905011634835 8078640583472857517452253)
              ·
                refine ⟨3029490218802321569044595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8078640583472857517452253 3029490218802321569044595)
                ·
                  refine ⟨4544235328203482353566893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029490218802321569044595 4544235328203482353566893)
                  ·
                    refine ⟨1704088248076305882587585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4544235328203482353566893 1704088248076305882587585)
                    ·
                      refine ⟨1278066186057229411940689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1704088248076305882587585 1278066186057229411940689)
                      ·
                        rfl

theorem cell23_2489025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_2489025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489025 prefixEnd_2489025 := by exact prefixLift 2489025
  have htrace : WordTrace (prefixWord ++ tailWord_2489025) baseStart_2489025 baseEnd_2489025 := by
    simpa [prefixWord, tailWord_2489025, baseEnd_2489025] using wordTrace_append hprefix tailTrace_2489025
  have hstable : (prefixWord ++ tailWord_2489025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489025).length < 2 ^ (prefixWord ++ tailWord_2489025).sum := by decide
  have hdescent : baseEnd_2489025 < baseStart_2489025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489038 : List Nat := [4, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2]
def baseStart_2489038 : Nat := 118140960795 + 2489038 * 2 ^ 59
def prefixEnd_2489038 : Nat := 4983230072969 + 3 ^ 40 * 2489038 * 2
def baseEnd_2489038 : Nat := 1278072861305737861078129

theorem tailTrace_2489038 : CollatzResearch.WordTrace tailWord_2489038 prefixEnd_2489038 1278072861305737861078129 := by
  unfold tailWord_2489038
  simp only [CollatzResearch.WordTrace]
  refine ⟨11347834244580986836507471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60521782637765263128039845 11347834244580986836507471)
  ·
    refine ⟨17021751366871480254761207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11347834244580986836507471 17021751366871480254761207)
    ·
      refine ⟨25532627050307220382141811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17021751366871480254761207 25532627050307220382141811)
      ·
        refine ⟨38298940575460830573212717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25532627050307220382141811 38298940575460830573212717)
        ·
          refine ⟨14362102715797811464954769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38298940575460830573212717 14362102715797811464954769)
          ·
            refine ⟨10771577036848358598716077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14362102715797811464954769 10771577036848358598716077)
            ·
              refine ⟨4039341388818134474518529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10771577036848358598716077 4039341388818134474518529)
              ·
                refine ⟨3029506041613600855888897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039341388818134474518529 3029506041613600855888897)
                ·
                  refine ⟨2272129531210200641916673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3029506041613600855888897 2272129531210200641916673)
                  ·
                    refine ⟨1704097148407650481437505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2272129531210200641916673 1704097148407650481437505)
                    ·
                      refine ⟨1278072861305737861078129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1704097148407650481437505 1278072861305737861078129)
                      ·
                        rfl

theorem cell23_2489038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_2489038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489038 prefixEnd_2489038 := by exact prefixLift 2489038
  have htrace : WordTrace (prefixWord ++ tailWord_2489038) baseStart_2489038 baseEnd_2489038 := by
    simpa [prefixWord, tailWord_2489038, baseEnd_2489038] using wordTrace_append hprefix tailTrace_2489038
  have hstable : (prefixWord ++ tailWord_2489038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489038).length < 2 ^ (prefixWord ++ tailWord_2489038).sum := by decide
  have hdescent : baseEnd_2489038 < baseStart_2489038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489057 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 1, 7]
def baseStart_2489057 : Nat := 118140960795 + 2489057 * 2 ^ 59
def prefixEnd_2489057 : Nat := 4983230072969 + 3 ^ 40 * 2489057 * 2
def baseEnd_2489057 : Nat := 426027539146057762246847

theorem tailTrace_2489057 : CollatzResearch.WordTrace tailWord_2489057 prefixEnd_2489057 426027539146057762246847 := by
  unfold tailWord_2489057
  simp only [CollatzResearch.WordTrace]
  refine ⟨90783366943579060937001425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60522244629052707291334283 90783366943579060937001425)
  ·
    refine ⟨68087525207684295702751069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90783366943579060937001425 68087525207684295702751069)
    ·
      refine ⟨25532821952881610888531651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68087525207684295702751069 25532821952881610888531651)
      ·
        refine ⟨38299232929322416332797477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25532821952881610888531651 38299232929322416332797477)
        ·
          refine ⟨7181106174247953062399527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38299232929322416332797477 7181106174247953062399527)
          ·
            refine ⟨10771659261371929593599291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7181106174247953062399527 10771659261371929593599291)
            ·
              refine ⟨16157488892057894390398937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10771659261371929593599291 16157488892057894390398937)
              ·
                refine ⟨12118116669043420792799203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16157488892057894390398937 12118116669043420792799203)
                ·
                  refine ⟨18177175003565131189198805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12118116669043420792799203 18177175003565131189198805)
                  ·
                    refine ⟨426027539146057762246847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18177175003565131189198805 426027539146057762246847)
                    ·
                      rfl

theorem cell23_2489057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_2489057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489057 prefixEnd_2489057 := by exact prefixLift 2489057
  have htrace : WordTrace (prefixWord ++ tailWord_2489057) baseStart_2489057 baseEnd_2489057 := by
    simpa [prefixWord, tailWord_2489057, baseEnd_2489057] using wordTrace_append hprefix tailTrace_2489057
  have hstable : (prefixWord ++ tailWord_2489057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489057).length < 2 ^ (prefixWord ++ tailWord_2489057).sum := by decide
  have hdescent : baseEnd_2489057 < baseStart_2489057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489114 : List Nat := [3, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3]
def baseStart_2489114 : Nat := 118140960795 + 2489114 * 2 ^ 59
def prefixEnd_2489114 : Nat := 4983230072969 + 3 ^ 40 * 2489114 * 2
def baseEnd_2489114 : Nat := 1278111885835479563727779

theorem tailTrace_2489114 : CollatzResearch.WordTrace tailWord_2489114 prefixEnd_2489114 1278111885835479563727779 := by
  unfold tailWord_2489114
  simp only [CollatzResearch.WordTrace]
  refine ⟨22696361476093139917956599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60523630602915039781217597 22696361476093139917956599)
  ·
    refine ⟨34044542214139709876934899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22696361476093139917956599 34044542214139709876934899)
    ·
      refine ⟨51066813321209564815402349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34044542214139709876934899 51066813321209564815402349)
      ·
        refine ⟨19150054995453586805775881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51066813321209564815402349 19150054995453586805775881)
        ·
          refine ⟨14362541246590190104331911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19150054995453586805775881 14362541246590190104331911)
          ·
            refine ⟨21543811869885285156497867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14362541246590190104331911 21543811869885285156497867)
            ·
              refine ⟨32315717804827927734746801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21543811869885285156497867 32315717804827927734746801)
              ·
                refine ⟨24236788353620945801060101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32315717804827927734746801 24236788353620945801060101)
                ·
                  refine ⟨4544397816303927337698769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24236788353620945801060101 4544397816303927337698769)
                  ·
                    refine ⟨3408298362227945503274077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4544397816303927337698769 3408298362227945503274077)
                    ·
                      refine ⟨1278111885835479563727779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3408298362227945503274077 1278111885835479563727779)
                      ·
                        rfl

theorem cell23_2489114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_2489114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489114 prefixEnd_2489114 := by exact prefixLift 2489114
  have htrace : WordTrace (prefixWord ++ tailWord_2489114) baseStart_2489114 baseEnd_2489114 := by
    simpa [prefixWord, tailWord_2489114, baseEnd_2489114] using wordTrace_append hprefix tailTrace_2489114
  have hstable : (prefixWord ++ tailWord_2489114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489114).length < 2 ^ (prefixWord ++ tailWord_2489114).sum := by decide
  have hdescent : baseEnd_2489114 < baseStart_2489114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489164 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 3, 5]
def baseStart_2489164 : Nat := 118140960795 + 2489164 * 2 ^ 59
def prefixEnd_2489164 : Nat := 4983230072969 + 3 ^ 40 * 2489164 * 2
def baseEnd_2489164 : Nat := 426045853289401456034183

theorem tailTrace_2489164 : CollatzResearch.WordTrace tailWord_2489164 prefixEnd_2489164 426045853289401456034183 := by
  unfold tailWord_2489164
  simp only [CollatzResearch.WordTrace]
  refine ⟨45393634777095709105573273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60524846369460945474097697 45393634777095709105573273)
  ·
    refine ⟨34045226082821781829179955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45393634777095709105573273 34045226082821781829179955)
    ·
      refine ⟨51067839124232672743769933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34045226082821781829179955 51067839124232672743769933)
      ·
        refine ⟨19150439671587252278913725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51067839124232672743769933 19150439671587252278913725)
        ·
          refine ⟨7181414876845219604592647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19150439671587252278913725 7181414876845219604592647)
          ·
            refine ⟨10772122315267829406888971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7181414876845219604592647 10772122315267829406888971)
            ·
              refine ⟨16158183472901744110333457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10772122315267829406888971 16158183472901744110333457)
              ·
                refine ⟨12118637604676308082750093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16158183472901744110333457 12118637604676308082750093)
                ·
                  refine ⟨4544489101753615531031285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12118637604676308082750093 4544489101753615531031285)
                  ·
                    refine ⟨426045853289401456034183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4544489101753615531031285 426045853289401456034183)
                    ·
                      rfl

theorem cell23_2489164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 3, 5].length) (baseStart_2489164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489164 prefixEnd_2489164 := by exact prefixLift 2489164
  have htrace : WordTrace (prefixWord ++ tailWord_2489164) baseStart_2489164 baseEnd_2489164 := by
    simpa [prefixWord, tailWord_2489164, baseEnd_2489164] using wordTrace_append hprefix tailTrace_2489164
  have hstable : (prefixWord ++ tailWord_2489164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489164).length < 2 ^ (prefixWord ++ tailWord_2489164).sum := by decide
  have hdescent : baseEnd_2489164 < baseStart_2489164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489184 : List Nat := [2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 4]
def baseStart_2489184 : Nat := 118140960795 + 2489184 * 2 ^ 59
def prefixEnd_2489184 : Nat := 4983230072969 + 3 ^ 40 * 2489184 * 2
def baseEnd_2489184 : Nat := 1278147829481294289852457

theorem tailTrace_2489184 : CollatzResearch.WordTrace tailWord_2489184 prefixEnd_2489184 1278147829481294289852457 := by
  unfold tailWord_2489184
  simp only [CollatzResearch.WordTrace]
  refine ⟨45393999507059480813437303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60525332676079307751249737 45393999507059480813437303)
  ·
    refine ⟨68090999260589221220155955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45393999507059480813437303 68090999260589221220155955)
    ·
      refine ⟨102136498890883831830233933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68090999260589221220155955 102136498890883831830233933)
      ·
        refine ⟨38301187084081436936337725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102136498890883831830233933 38301187084081436936337725)
        ·
          refine ⟨14362945156530538851126647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38301187084081436936337725 14362945156530538851126647)
          ·
            refine ⟨21544417734795808276689971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14362945156530538851126647 21544417734795808276689971)
            ·
              refine ⟨32316626602193712415034957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21544417734795808276689971 32316626602193712415034957)
              ·
                refine ⟨12118734975822642155638109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32316626602193712415034957 12118734975822642155638109)
                ·
                  refine ⟨4544525615933490808364291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12118734975822642155638109 4544525615933490808364291)
                  ·
                    refine ⟨6816788423900236212546437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4544525615933490808364291 6816788423900236212546437)
                    ·
                      refine ⟨1278147829481294289852457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6816788423900236212546437 1278147829481294289852457)
                      ·
                        rfl

theorem cell23_2489184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_2489184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489184 prefixEnd_2489184 := by exact prefixLift 2489184
  have htrace : WordTrace (prefixWord ++ tailWord_2489184) baseStart_2489184 baseEnd_2489184 := by
    simpa [prefixWord, tailWord_2489184, baseEnd_2489184] using wordTrace_append hprefix tailTrace_2489184
  have hstable : (prefixWord ++ tailWord_2489184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489184).length < 2 ^ (prefixWord ++ tailWord_2489184).sum := by decide
  have hdescent : baseEnd_2489184 < baseStart_2489184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489188 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 2, 3, 2]
def baseStart_2489188 : Nat := 118140960795 + 2489188 * 2 ^ 59
def prefixEnd_2489188 : Nat := 4983230072969 + 3 ^ 40 * 2489188 * 2
def baseEnd_2489188 : Nat := 1278149883403912274202439

theorem tailTrace_2489188 : CollatzResearch.WordTrace tailWord_2489188 prefixEnd_2489188 1278149883403912274202439 := by
  unfold tailWord_2489188
  simp only [CollatzResearch.WordTrace]
  refine ⟨45394072453052235155010109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60525429937402980206680145 45394072453052235155010109)
  ·
    refine ⟨17022777169894588183128791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45394072453052235155010109 17022777169894588183128791)
    ·
      refine ⟨25534165754841882274693187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17022777169894588183128791 25534165754841882274693187)
      ·
        refine ⟨38301248632262823412039781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25534165754841882274693187 38301248632262823412039781)
        ·
          refine ⟨7181484118549279389757459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38301248632262823412039781 7181484118549279389757459)
          ·
            refine ⟨10772226177823919084636189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7181484118549279389757459 10772226177823919084636189)
            ·
              refine ⟨4039584816683969656738571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10772226177823919084636189 4039584816683969656738571)
              ·
                refine ⟨6059377225025954485107857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4039584816683969656738571 6059377225025954485107857)
                ·
                  refine ⟨4544532918769465863830893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6059377225025954485107857 4544532918769465863830893)
                  ·
                    refine ⟨1704199844538549698936585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4544532918769465863830893 1704199844538549698936585)
                    ·
                      refine ⟨1278149883403912274202439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1704199844538549698936585 1278149883403912274202439)
                      ·
                        rfl

theorem cell23_2489188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_2489188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489188 prefixEnd_2489188 := by exact prefixLift 2489188
  have htrace : WordTrace (prefixWord ++ tailWord_2489188) baseStart_2489188 baseEnd_2489188 := by
    simpa [prefixWord, tailWord_2489188, baseEnd_2489188] using wordTrace_append hprefix tailTrace_2489188
  have hstable : (prefixWord ++ tailWord_2489188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489188).length < 2 ^ (prefixWord ++ tailWord_2489188).sum := by decide
  have hdescent : baseEnd_2489188 < baseStart_2489188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489198 : List Nat := [4, 1, 2, 3, 2, 1, 1, 3, 1, 5]
def baseStart_2489198 : Nat := 118140960795 + 2489198 * 2 ^ 59
def prefixEnd_2489198 : Nat := 4983230072969 + 3 ^ 40 * 2489198 * 2
def baseEnd_2489198 : Nat := 426051672736819078359131

theorem tailTrace_2489198 : CollatzResearch.WordTrace tailWord_2489198 prefixEnd_2489198 426051672736819078359131 := by
  unfold tailWord_2489198
  simp only [CollatzResearch.WordTrace]
  refine ⟨11348563704508530252235531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60525673090712161345256165 11348563704508530252235531)
  ·
    refine ⟨17022845556762795378353297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11348563704508530252235531 17022845556762795378353297)
    ·
      refine ⟨12767134167572096533764973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17022845556762795378353297 12767134167572096533764973)
      ·
        refine ⟨4787675312839536200161865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12767134167572096533764973 4787675312839536200161865)
        ·
          refine ⟨3590756484629652150121399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4787675312839536200161865 3590756484629652150121399)
          ·
            refine ⟨5386134726944478225182099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590756484629652150121399 5386134726944478225182099)
            ·
              refine ⟨8079202090416717337773149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5386134726944478225182099 8079202090416717337773149)
              ·
                refine ⟨3029700783906269001664931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8079202090416717337773149 3029700783906269001664931)
                ·
                  refine ⟨4544551175859403502497397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029700783906269001664931 4544551175859403502497397)
                  ·
                    refine ⟨426051672736819078359131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4544551175859403502497397 426051672736819078359131)
                    ·
                      rfl

theorem cell23_2489198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_2489198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489198 prefixEnd_2489198 := by exact prefixLift 2489198
  have htrace : WordTrace (prefixWord ++ tailWord_2489198) baseStart_2489198 baseEnd_2489198 := by
    simpa [prefixWord, tailWord_2489198, baseEnd_2489198] using wordTrace_append hprefix tailTrace_2489198
  have hstable : (prefixWord ++ tailWord_2489198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489198).length < 2 ^ (prefixWord ++ tailWord_2489198).sum := by decide
  have hdescent : baseEnd_2489198 < baseStart_2489198 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489201 : List Nat := [1, 2, 2, 2, 1, 5, 1, 3, 1, 1, 4]
def baseStart_2489201 : Nat := 118140960795 + 2489201 * 2 ^ 59
def prefixEnd_2489201 : Nat := 4983230072969 + 3 ^ 40 * 2489201 * 2
def baseEnd_2489201 : Nat := 1278156558652420723339879

theorem tailTrace_2489201 : CollatzResearch.WordTrace tailWord_2489201 prefixEnd_2489201 1278156558652420723339879 := by
  unfold tailWord_2489201
  simp only [CollatzResearch.WordTrace]
  refine ⟨90788619055057373530243457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60525746036704915686828971 90788619055057373530243457)
  ·
    refine ⟨68091464291293030147682593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90788619055057373530243457 68091464291293030147682593)
    ·
      refine ⟨51068598218469772610761945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68091464291293030147682593 51068598218469772610761945)
      ·
        refine ⟨38301448663852329458071459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51068598218469772610761945 38301448663852329458071459)
        ·
          refine ⟨57452172995778494187107189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38301448663852329458071459 57452172995778494187107189)
          ·
            refine ⟨5386141218354233830041299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57452172995778494187107189 5386141218354233830041299)
            ·
              refine ⟨8079211827531350745061949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5386141218354233830041299 8079211827531350745061949)
              ·
                refine ⟨3029704435324256529398231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8079211827531350745061949 3029704435324256529398231)
                ·
                  refine ⟨4544556652986384794097347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029704435324256529398231 4544556652986384794097347)
                  ·
                    refine ⟨6816834979479577191146021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4544556652986384794097347 6816834979479577191146021)
                    ·
                      refine ⟨1278156558652420723339879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6816834979479577191146021 1278156558652420723339879)
                      ·
                        rfl

theorem cell23_2489201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_2489201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489201 prefixEnd_2489201 := by exact prefixLift 2489201
  have htrace : WordTrace (prefixWord ++ tailWord_2489201) baseStart_2489201 baseEnd_2489201 := by
    simpa [prefixWord, tailWord_2489201, baseEnd_2489201] using wordTrace_append hprefix tailTrace_2489201
  have hstable : (prefixWord ++ tailWord_2489201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489201).length < 2 ^ (prefixWord ++ tailWord_2489201).sum := by decide
  have hdescent : baseEnd_2489201 < baseStart_2489201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489211 : List Nat := [1, 1, 1, 1, 1, 5, 5, 2, 2, 4]
def baseStart_2489211 : Nat := 118140960795 + 2489211 * 2 ^ 59
def prefixEnd_2489211 : Nat := 4983230072969 + 3 ^ 40 * 2489211 * 2
def baseEnd_2489211 : Nat := 426053897819655228071611

theorem tailTrace_2489211 : CollatzResearch.WordTrace tailWord_2489211 prefixEnd_2489211 426053897819655228071611 := by
  unfold tailWord_2489211
  simp only [CollatzResearch.WordTrace]
  refine ⟨90788983785021145238107487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60525989190014096825404991 90788983785021145238107487)
  ·
    refine ⟨136183475677531717857161231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90788983785021145238107487 136183475677531717857161231)
    ·
      refine ⟨204275213516297576785741847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136183475677531717857161231 204275213516297576785741847)
      ·
        refine ⟨306412820274446365178612771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204275213516297576785741847 306412820274446365178612771)
        ·
          refine ⟨459619230411669547767919157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306412820274446365178612771 459619230411669547767919157)
          ·
            refine ⟨43089302851094020103242421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 459619230411669547767919157 43089302851094020103242421)
            ·
              refine ⟨4039622142290064384678977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43089302851094020103242421 4039622142290064384678977)
              ·
                refine ⟨3029716606717548288509233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039622142290064384678977 3029716606717548288509233)
                ·
                  refine ⟨2272287455038161216381925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3029716606717548288509233 2272287455038161216381925)
                  ·
                    refine ⟨426053897819655228071611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2272287455038161216381925 426053897819655228071611)
                    ·
                      rfl

theorem cell23_2489211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 4].length) (baseStart_2489211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489211 prefixEnd_2489211 := by exact prefixLift 2489211
  have htrace : WordTrace (prefixWord ++ tailWord_2489211) baseStart_2489211 baseEnd_2489211 := by
    simpa [prefixWord, tailWord_2489211, baseEnd_2489211] using wordTrace_append hprefix tailTrace_2489211
  have hstable : (prefixWord ++ tailWord_2489211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489211).length < 2 ^ (prefixWord ++ tailWord_2489211).sum := by decide
  have hdescent : baseEnd_2489211 < baseStart_2489211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489251 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 4, 1, 3]
def baseStart_2489251 : Nat := 118140960795 + 2489251 * 2 ^ 59
def prefixEnd_2489251 : Nat := 4983230072969 + 3 ^ 40 * 2489251 * 2
def baseEnd_2489251 : Nat := 1278182232685145527714649

theorem tailTrace_2489251 : CollatzResearch.WordTrace tailWord_2489251 prefixEnd_2489251 1278182232685145527714649 := by
  unfold tailWord_2489251
  simp only [CollatzResearch.WordTrace]
  refine ⟨90790442704876232069563607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60526961803250821379709071 90790442704876232069563607)
  ·
    refine ⟨136185664057314348104345411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90790442704876232069563607 136185664057314348104345411)
    ·
      refine ⟨204278496085971522156518117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136185664057314348104345411 204278496085971522156518117)
      ·
        refine ⟨38302218016119660404347147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 204278496085971522156518117 38302218016119660404347147)
        ·
          refine ⟨57453327024179490606520721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38302218016119660404347147 57453327024179490606520721)
          ·
            refine ⟨43089995268134617954890541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57453327024179490606520721 43089995268134617954890541)
            ·
              refine ⟨16158748225550481733083953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43089995268134617954890541 16158748225550481733083953)
              ·
                refine ⟨12119061169162861299812965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16158748225550481733083953 12119061169162861299812965)
                ·
                  refine ⟨2272323969218036493714931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12119061169162861299812965 2272323969218036493714931)
                  ·
                    refine ⟨3408485953827054740572397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2272323969218036493714931 3408485953827054740572397)
                    ·
                      refine ⟨1278182232685145527714649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3408485953827054740572397 1278182232685145527714649)
                      ·
                        rfl

theorem cell23_2489251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_2489251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489251 prefixEnd_2489251 := by exact prefixLift 2489251
  have htrace : WordTrace (prefixWord ++ tailWord_2489251) baseStart_2489251 baseEnd_2489251 := by
    simpa [prefixWord, tailWord_2489251, baseEnd_2489251] using wordTrace_append hprefix tailTrace_2489251
  have hstable : (prefixWord ++ tailWord_2489251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489251).length < 2 ^ (prefixWord ++ tailWord_2489251).sum := by decide
  have hdescent : baseEnd_2489251 < baseStart_2489251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489274 : List Nat := [3, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4]
def baseStart_2489274 : Nat := 118140960795 + 2489274 * 2 ^ 59
def prefixEnd_2489274 : Nat := 4983230072969 + 3 ^ 40 * 2489274 * 2
def baseEnd_2489274 : Nat := 1278194042740198937727043

theorem tailTrace_2489274 : CollatzResearch.WordTrace tailWord_2489274 prefixEnd_2489274 1278194042740198937727043 := by
  unfold tailWord_2489274
  simp only [CollatzResearch.WordTrace]
  refine ⟨22697820395948226749412719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60527521055861937998433917 22697820395948226749412719)
  ·
    refine ⟨34046730593922340124119079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22697820395948226749412719 34046730593922340124119079)
    ·
      refine ⟨51070095890883510186178619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34046730593922340124119079 51070095890883510186178619)
      ·
        refine ⟨76605143836325265279267929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51070095890883510186178619 76605143836325265279267929)
        ·
          refine ⟨57453857877243948959450947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76605143836325265279267929 57453857877243948959450947)
          ·
            refine ⟨86180786815865923439176421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57453857877243948959450947 86180786815865923439176421)
            ·
              refine ⟨16158897527974860644845579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86180786815865923439176421 16158897527974860644845579)
              ·
                refine ⟨24238346291962290967268369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16158897527974860644845579 24238346291962290967268369)
                ·
                  refine ⟨18178759718971718225451277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24238346291962290967268369 18178759718971718225451277)
                  ·
                    refine ⟨6817034894614394334544229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18178759718971718225451277 6817034894614394334544229)
                    ·
                      refine ⟨1278194042740198937727043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6817034894614394334544229 1278194042740198937727043)
                      ·
                        rfl

theorem cell23_2489274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_2489274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489274 prefixEnd_2489274 := by exact prefixLift 2489274
  have htrace : WordTrace (prefixWord ++ tailWord_2489274) baseStart_2489274 baseEnd_2489274 := by
    simpa [prefixWord, tailWord_2489274, baseEnd_2489274] using wordTrace_append hprefix tailTrace_2489274
  have hstable : (prefixWord ++ tailWord_2489274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489274).length < 2 ^ (prefixWord ++ tailWord_2489274).sum := by decide
  have hdescent : baseEnd_2489274 < baseStart_2489274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489278 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2]
def baseStart_2489278 : Nat := 118140960795 + 2489278 * 2 ^ 59
def prefixEnd_2489278 : Nat := 4983230072969 + 3 ^ 40 * 2489278 * 2
def baseEnd_2489278 : Nat := 1278196096662816922077025

theorem tailTrace_2489278 : CollatzResearch.WordTrace tailWord_2489278 prefixEnd_2489278 1278196096662816922077025 := by
  unfold tailWord_2489278
  simp only [CollatzResearch.WordTrace]
  refine ⟨11348928434472301960099561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60527618317185610453864325 11348928434472301960099561)
  ·
    refine ⟨8511696325854226470074671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11348928434472301960099561 8511696325854226470074671)
    ·
      refine ⟨12767544488781339705112007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8511696325854226470074671 12767544488781339705112007)
      ·
        refine ⟨19151316733172009557668011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12767544488781339705112007 19151316733172009557668011)
        ·
          refine ⟨28726975099758014336502017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19151316733172009557668011 28726975099758014336502017)
          ·
            refine ⟨21545231324818510752376513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28726975099758014336502017 21545231324818510752376513)
            ·
              refine ⟨16158923493613883064282385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21545231324818510752376513 16158923493613883064282385)
              ·
                refine ⟨12119192620210412298211789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16158923493613883064282385 12119192620210412298211789)
                ·
                  refine ⟨4544697232578904611829421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12119192620210412298211789 4544697232578904611829421)
                  ·
                    refine ⟨1704261462217089229436033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4544697232578904611829421 1704261462217089229436033)
                    ·
                      refine ⟨1278196096662816922077025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1704261462217089229436033 1278196096662816922077025)
                      ·
                        rfl

theorem cell23_2489278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_2489278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489278 prefixEnd_2489278 := by exact prefixLift 2489278
  have htrace : WordTrace (prefixWord ++ tailWord_2489278) baseStart_2489278 baseEnd_2489278 := by
    simpa [prefixWord, tailWord_2489278, baseEnd_2489278] using wordTrace_append hprefix tailTrace_2489278
  have hstable : (prefixWord ++ tailWord_2489278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489278).length < 2 ^ (prefixWord ++ tailWord_2489278).sum := by decide
  have hdescent : baseEnd_2489278 < baseStart_2489278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489286 : List Nat := [6, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_2489286 : Nat := 118140960795 + 2489286 * 2 ^ 59
def prefixEnd_2489286 : Nat := 4983230072969 + 3 ^ 40 * 2489286 * 2
def baseEnd_2489286 : Nat := 1278200204508052890776989

theorem tailTrace_2489286 : CollatzResearch.WordTrace tailWord_2489286 prefixEnd_2489286 1278200204508052890776989 := by
  unfold tailWord_2489286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2837241226867169782721491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60527812839832955364725141 2837241226867169782721491)
  ·
    refine ⟨4255861840300754674082237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2837241226867169782721491 4255861840300754674082237)
    ·
      refine ⟨1595948190112783002780839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4255861840300754674082237 1595948190112783002780839)
      ·
        refine ⟨2393922285169174504171259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1595948190112783002780839 2393922285169174504171259)
        ·
          refine ⟨3590883427753761756256889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393922285169174504171259 3590883427753761756256889)
          ·
            refine ⟨2693162570815321317192667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3590883427753761756256889 2693162570815321317192667)
            ·
              refine ⟨4039743856222981975789001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2693162570815321317192667 4039743856222981975789001)
              ·
                refine ⟨3029807892167236481841751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039743856222981975789001 3029807892167236481841751)
                ·
                  refine ⟨4544711838250854722762627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029807892167236481841751 4544711838250854722762627)
                  ·
                    refine ⟨6817067757376282084143941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4544711838250854722762627 6817067757376282084143941)
                    ·
                      refine ⟨1278200204508052890776989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6817067757376282084143941 1278200204508052890776989)
                      ·
                        rfl

theorem cell23_2489286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_2489286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489286 prefixEnd_2489286 := by exact prefixLift 2489286
  have htrace : WordTrace (prefixWord ++ tailWord_2489286) baseStart_2489286 baseEnd_2489286 := by
    simpa [prefixWord, tailWord_2489286, baseEnd_2489286] using wordTrace_append hprefix tailTrace_2489286
  have hstable : (prefixWord ++ tailWord_2489286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489286).length < 2 ^ (prefixWord ++ tailWord_2489286).sum := by decide
  have hdescent : baseEnd_2489286 < baseStart_2489286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489295 : List Nat := [1, 1, 2, 1, 1, 8, 1, 2, 1, 3, 2]
def baseStart_2489295 : Nat := 118140960795 + 2489295 * 2 ^ 59
def prefixEnd_2489295 : Nat := 4983230072969 + 3 ^ 40 * 2489295 * 2
def baseEnd_2489295 : Nat := 1278204825833943355564447

theorem tailTrace_2489295 : CollatzResearch.WordTrace tailWord_2489295 prefixEnd_2489295 1278204825833943355564447 := by
  unfold tailWord_2489295
  simp only [CollatzResearch.WordTrace]
  refine ⟨90792047516716827584165339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60528031677811218389443559 90792047516716827584165339)
  ·
    refine ⟨136188071275075241376248009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90792047516716827584165339 136188071275075241376248009)
    ·
      refine ⟨102141053456306431032186007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136188071275075241376248009 102141053456306431032186007)
      ·
        refine ⟨153211580184459646548279011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102141053456306431032186007 153211580184459646548279011)
        ·
          refine ⟨229817370276689469822418517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153211580184459646548279011 229817370276689469822418517)
          ·
            refine ⟨2693172307929954724481467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 229817370276689469822418517 2693172307929954724481467)
            ·
              refine ⟨4039758461894932086722201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2693172307929954724481467 4039758461894932086722201)
              ·
                refine ⟨3029818846421199065041651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039758461894932086722201 3029818846421199065041651)
                ·
                  refine ⟨4544728269631798597562477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3029818846421199065041651 4544728269631798597562477)
                  ·
                    refine ⟨1704273101111924474085929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4544728269631798597562477 1704273101111924474085929)
                    ·
                      refine ⟨1278204825833943355564447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1704273101111924474085929 1278204825833943355564447)
                      ·
                        rfl

theorem cell23_2489295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 3, 2].length) (baseStart_2489295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489295 prefixEnd_2489295 := by exact prefixLift 2489295
  have htrace : WordTrace (prefixWord ++ tailWord_2489295) baseStart_2489295 baseEnd_2489295 := by
    simpa [prefixWord, tailWord_2489295, baseEnd_2489295] using wordTrace_append hprefix tailTrace_2489295
  have hstable : (prefixWord ++ tailWord_2489295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489295).length < 2 ^ (prefixWord ++ tailWord_2489295).sum := by decide
  have hdescent : baseEnd_2489295 < baseStart_2489295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489342 : List Nat := [4, 2, 2, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_2489342 : Nat := 118140960795 + 2489342 * 2 ^ 59
def prefixEnd_2489342 : Nat := 4983230072969 + 3 ^ 40 * 2489342 * 2
def baseEnd_2489342 : Nat := 1278228959424704671676731

theorem tailTrace_2489342 : CollatzResearch.WordTrace tailWord_2489342 prefixEnd_2489342 1278228959424704671676731 := by
  unfold tailWord_2489342
  simp only [CollatzResearch.WordTrace]
  refine ⟨11349220218443319326390785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60529174498364369740750853 11349220218443319326390785)
  ·
    refine ⟨8511915163832489494793089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11349220218443319326390785 8511915163832489494793089)
    ·
      refine ⟨6383936372874367121094817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8511915163832489494793089 6383936372874367121094817)
      ·
        refine ⟨4787952279655775340821113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6383936372874367121094817 4787952279655775340821113)
        ·
          refine ⟨3590964209741831505615835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4787952279655775340821113 3590964209741831505615835)
          ·
            refine ⟨5386446314612747258423753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590964209741831505615835 5386446314612747258423753)
            ·
              refine ⟨4039834735959560443817815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5386446314612747258423753 4039834735959560443817815)
              ·
                refine ⟨6059752103939340665726723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4039834735959560443817815 6059752103939340665726723)
                ·
                  refine ⟨9089628155909010998590085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6059752103939340665726723 9089628155909010998590085)
                  ·
                    refine ⟨1704305279232939562235641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9089628155909010998590085 1704305279232939562235641)
                    ·
                      refine ⟨1278228959424704671676731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1704305279232939562235641 1278228959424704671676731)
                      ·
                        rfl

theorem cell23_2489342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_2489342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489342 prefixEnd_2489342 := by exact prefixLift 2489342
  have htrace : WordTrace (prefixWord ++ tailWord_2489342) baseStart_2489342 baseEnd_2489342 := by
    simpa [prefixWord, tailWord_2489342, baseEnd_2489342] using wordTrace_append hprefix tailTrace_2489342
  have hstable : (prefixWord ++ tailWord_2489342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489342).length < 2 ^ (prefixWord ++ tailWord_2489342).sum := by decide
  have hdescent : baseEnd_2489342 < baseStart_2489342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489376 : List Nat := [2, 1, 1, 7, 2, 1, 1, 2, 2, 2, 2]
def baseStart_2489376 : Nat := 118140960795 + 2489376 * 2 ^ 59
def prefixEnd_2489376 : Nat := 4983230072969 + 3 ^ 40 * 2489376 * 2
def baseEnd_2489376 : Nat := 1278246417766957538651575

theorem tailTrace_2489376 : CollatzResearch.WordTrace tailWord_2489376 prefixEnd_2489376 1278246417766957538651575 := by
  unfold tailWord_2489376
  simp only [CollatzResearch.WordTrace]
  refine ⟨45397500914711689208931991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60530001219615585611909321 45397500914711689208931991)
  ·
    refine ⟨68096251372067533813397987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45397500914711689208931991 68096251372067533813397987)
    ·
      refine ⟨102144377058101300720096981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68096251372067533813397987 102144377058101300720096981)
      ·
        refine ⟨2394008837299249235627273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 102144377058101300720096981 2394008837299249235627273)
        ·
          refine ⟨1795506627974436926720455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2394008837299249235627273 1795506627974436926720455)
          ·
            refine ⟨2693259941961655390080683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1795506627974436926720455 2693259941961655390080683)
            ·
              refine ⟨4039889912942483085121025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2693259941961655390080683 4039889912942483085121025)
              ·
                refine ⟨3029917434706862313840769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4039889912942483085121025 3029917434706862313840769)
                ·
                  refine ⟨2272438076030146735380577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3029917434706862313840769 2272438076030146735380577)
                  ·
                    refine ⟨1704328557022610051535433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2272438076030146735380577 1704328557022610051535433)
                    ·
                      refine ⟨1278246417766957538651575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1704328557022610051535433 1278246417766957538651575)
                      ·
                        rfl

theorem cell23_2489376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_2489376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489376 prefixEnd_2489376 := by exact prefixLift 2489376
  have htrace : WordTrace (prefixWord ++ tailWord_2489376) baseStart_2489376 baseEnd_2489376 := by
    simpa [prefixWord, tailWord_2489376, baseEnd_2489376] using wordTrace_append hprefix tailTrace_2489376
  have hstable : (prefixWord ++ tailWord_2489376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489376).length < 2 ^ (prefixWord ++ tailWord_2489376).sum := by decide
  have hdescent : baseEnd_2489376 < baseStart_2489376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489381 : List Nat := [1, 3, 1, 2, 2, 2, 2, 1, 4, 1, 4]
def baseStart_2489381 : Nat := 118140960795 + 2489381 * 2 ^ 59
def prefixEnd_2489381 : Nat := 4983230072969 + 3 ^ 40 * 2489381 * 2
def baseEnd_2489381 : Nat := 1278248985170230019089051

theorem tailTrace_2489381 : CollatzResearch.WordTrace tailWord_2489381 prefixEnd_2489381 1278248985170230019089051 := by
  unfold tailWord_2489381
  simp only [CollatzResearch.WordTrace]
  refine ⟨90795184194405264271795997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60530122796270176181197331 90795184194405264271795997)
  ·
    refine ⟨34048194072901974101923499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90795184194405264271795997 34048194072901974101923499)
    ·
      refine ⟨51072291109352961152885249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34048194072901974101923499 51072291109352961152885249)
      ·
        refine ⟨38304218332014720864663937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51072291109352961152885249 38304218332014720864663937)
        ·
          refine ⟨28728163749011040648497953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38304218332014720864663937 28728163749011040648497953)
          ·
            refine ⟨21546122811758280486373465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28728163749011040648497953 21546122811758280486373465)
            ·
              refine ⟨16159592108818710364780099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21546122811758280486373465 16159592108818710364780099)
              ·
                refine ⟨24239388163228065547170149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16159592108818710364780099 24239388163228065547170149)
                ·
                  refine ⟨4544885280605262290094403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24239388163228065547170149 4544885280605262290094403)
                  ·
                    refine ⟨6817327920907893435141605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4544885280605262290094403 6817327920907893435141605)
                    ·
                      refine ⟨1278248985170230019089051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6817327920907893435141605 1278248985170230019089051)
                      ·
                        rfl

theorem cell23_2489381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_2489381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489381 prefixEnd_2489381 := by exact prefixLift 2489381
  have htrace : WordTrace (prefixWord ++ tailWord_2489381) baseStart_2489381 baseEnd_2489381 := by
    simpa [prefixWord, tailWord_2489381, baseEnd_2489381] using wordTrace_append hprefix tailTrace_2489381
  have hstable : (prefixWord ++ tailWord_2489381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489381).length < 2 ^ (prefixWord ++ tailWord_2489381).sum := by decide
  have hdescent : baseEnd_2489381 < baseStart_2489381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2489398 : List Nat := [5, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_2489398 : Nat := 118140960795 + 2489398 * 2 ^ 59
def prefixEnd_2489398 : Nat := 4983230072969 + 3 ^ 40 * 2489398 * 2
def baseEnd_2489398 : Nat := 1278257714341356452576473

theorem tailTrace_2489398 : CollatzResearch.WordTrace tailWord_2489398 prefixEnd_2489398 1278257714341356452576473 := by
  unfold tailWord_2489398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5674737764708979760947803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60530536156895784116776565 5674737764708979760947803)
  ·
    refine ⟨8512106647063469641421705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5674737764708979760947803 8512106647063469641421705)
    ·
      refine ⟨6384079985297602231066279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8512106647063469641421705 6384079985297602231066279)
      ·
        refine ⟨9576119977946403346599419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6384079985297602231066279 9576119977946403346599419)
        ·
          refine ⟨14364179966919605019899129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9576119977946403346599419 14364179966919605019899129)
          ·
            refine ⟨10773134975189703764924347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14364179966919605019899129 10773134975189703764924347)
            ·
              refine ⟨16159702462784555647386521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10773134975189703764924347 16159702462784555647386521)
              ·
                refine ⟨12119776847088416735539891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16159702462784555647386521 12119776847088416735539891)
                ·
                  refine ⟨18179665270632625103309837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12119776847088416735539891 18179665270632625103309837)
                  ·
                    refine ⟨6817374476487234413741189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18179665270632625103309837 6817374476487234413741189)
                    ·
                      refine ⟨1278257714341356452576473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6817374476487234413741189 1278257714341356452576473)
                      ·
                        rfl

theorem cell23_2489398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_2489398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2489398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2489398 prefixEnd_2489398 := by exact prefixLift 2489398
  have htrace : WordTrace (prefixWord ++ tailWord_2489398) baseStart_2489398 baseEnd_2489398 := by
    simpa [prefixWord, tailWord_2489398, baseEnd_2489398] using wordTrace_append hprefix tailTrace_2489398
  have hstable : (prefixWord ++ tailWord_2489398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2489398).length < 2 ^ (prefixWord ++ tailWord_2489398).sum := by decide
  have hdescent : baseEnd_2489398 < baseStart_2489398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2489398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
