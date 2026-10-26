import V185TrunkScan23Chunk0956

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5666159 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 2, 4, 2]
def baseStart_5666159 : Nat := 118140960795 + 5666159 * 2 ^ 59
def prefixEnd_5666159 : Nat := 4983230072969 + 3 ^ 40 * 5666159 * 2
def baseEnd_5666159 : Nat := 2909463031799001860554315

theorem tailTrace_5666159 : CollatzResearch.WordTrace tailWord_5666159 prefixEnd_5666159 2909463031799001860554315 := by
  unfold tailWord_5666159
  simp only [CollatzResearch.WordTrace]
  refine ⟨206661796679481120759545531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137774531119654080506363687 206661796679481120759545531)
  ·
    refine ⟨309992695019221681139318297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206661796679481120759545531 309992695019221681139318297)
    ·
      refine ⟨232494521264416260854488723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309992695019221681139318297 232494521264416260854488723)
      ·
        refine ⟨348741781896624391281733085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232494521264416260854488723 348741781896624391281733085)
        ·
          refine ⟨130778168211234146730649907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348741781896624391281733085 130778168211234146730649907)
          ·
            refine ⟨196167252316851220095974861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130778168211234146730649907 196167252316851220095974861)
            ·
              refine ⟨73562719618819207535990573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196167252316851220095974861 73562719618819207535990573)
              ·
                refine ⟨27586019857057202825996465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73562719618819207535990573 27586019857057202825996465)
                ·
                  refine ⟨20689514892792902119497349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27586019857057202825996465 20689514892792902119497349)
                  ·
                    refine ⟨3879284042398669147405753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20689514892792902119497349 3879284042398669147405753)
                    ·
                      refine ⟨2909463031799001860554315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3879284042398669147405753 2909463031799001860554315)
                      ·
                        rfl

theorem cell23_5666159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 4, 2].length) (baseStart_5666159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666159 prefixEnd_5666159 := by exact prefixLift 5666159
  have htrace : WordTrace (prefixWord ++ tailWord_5666159) baseStart_5666159 baseEnd_5666159 := by
    simpa [prefixWord, tailWord_5666159, baseEnd_5666159] using wordTrace_append hprefix tailTrace_5666159
  have hstable : (prefixWord ++ tailWord_5666159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666159).length < 2 ^ (prefixWord ++ tailWord_5666159).sum := by decide
  have hdescent : baseEnd_5666159 < baseStart_5666159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666169 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 3, 4]
def baseStart_5666169 : Nat := 118140960795 + 5666169 * 2 ^ 59
def prefixEnd_5666169 : Nat := 4983230072969 + 3 ^ 40 * 5666169 * 2
def baseEnd_5666169 : Nat := 969822722201848940476423

theorem tailTrace_5666169 : CollatzResearch.WordTrace tailWord_5666169 prefixEnd_5666169 969822722201848940476423 := by
  unfold tailWord_5666169
  simp only [CollatzResearch.WordTrace]
  refine ⟨206662161409444892467409561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137774774272963261644939707 206662161409444892467409561)
  ·
    refine ⟨154996621057083669350557171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206662161409444892467409561 154996621057083669350557171)
    ·
      refine ⟨232494931585625504025835757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154996621057083669350557171 232494931585625504025835757)
      ·
        refine ⟨87185599344609564009688409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232494931585625504025835757 87185599344609564009688409)
        ·
          refine ⟨65389199508457173007266307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87185599344609564009688409 65389199508457173007266307)
          ·
            refine ⟨98083799262685759510899461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65389199508457173007266307 98083799262685759510899461)
            ·
              refine ⟨18390712361753579908293649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98083799262685759510899461 18390712361753579908293649)
              ·
                refine ⟨13793034271315184931220237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18390712361753579908293649 13793034271315184931220237)
                ·
                  refine ⟨5172387851743194349207589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13793034271315184931220237 5172387851743194349207589)
                  ·
                    refine ⟨969822722201848940476423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5172387851743194349207589 969822722201848940476423)
                    ·
                      rfl

theorem cell23_5666169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 3, 4].length) (baseStart_5666169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666169 prefixEnd_5666169 := by exact prefixLift 5666169
  have htrace : WordTrace (prefixWord ++ tailWord_5666169) baseStart_5666169 baseEnd_5666169 := by
    simpa [prefixWord, tailWord_5666169, baseEnd_5666169] using wordTrace_append hprefix tailTrace_5666169
  have hstable : (prefixWord ++ tailWord_5666169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666169).length < 2 ^ (prefixWord ++ tailWord_5666169).sum := by decide
  have hdescent : baseEnd_5666169 < baseStart_5666169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666172 : List Nat := [2, 2, 2, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_5666172 : Nat := 118140960795 + 5666172 * 2 ^ 59
def prefixEnd_5666172 : Nat := 4983230072969 + 3 ^ 40 * 5666172 * 2
def baseEnd_5666172 : Nat := 2909469707047510309691755

theorem tailTrace_5666172 : CollatzResearch.WordTrace tailWord_5666172 prefixEnd_5666172 2909469707047510309691755 := by
  unfold tailWord_5666172
  simp only [CollatzResearch.WordTrace]
  refine ⟨103331135414217011989884385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137774847218956015986512513 103331135414217011989884385)
  ·
    refine ⟨77498351560662758992413289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103331135414217011989884385 77498351560662758992413289)
    ·
      refine ⟨58123763670497069244309967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77498351560662758992413289 58123763670497069244309967)
      ·
        refine ⟨87185645505745603866464951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58123763670497069244309967 87185645505745603866464951)
        ·
          refine ⟨130778468258618405799697427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87185645505745603866464951 130778468258618405799697427)
          ·
            refine ⟨196167702387927608699546141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130778468258618405799697427 196167702387927608699546141)
            ·
              refine ⟨73562888395472853262329803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196167702387927608699546141 73562888395472853262329803)
              ·
                refine ⟨110344332593209279893494705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73562888395472853262329803 110344332593209279893494705)
                ·
                  refine ⟨82758249444906959920121029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110344332593209279893494705 82758249444906959920121029)
                  ·
                    refine ⟨15517171770920054985022693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82758249444906959920121029 15517171770920054985022693)
                    ·
                      refine ⟨2909469707047510309691755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15517171770920054985022693 2909469707047510309691755)
                      ·
                        rfl

theorem cell23_5666172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_5666172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666172 prefixEnd_5666172 := by exact prefixLift 5666172
  have htrace : WordTrace (prefixWord ++ tailWord_5666172) baseStart_5666172 baseEnd_5666172 := by
    simpa [prefixWord, tailWord_5666172, baseEnd_5666172] using wordTrace_append hprefix tailTrace_5666172
  have hstable : (prefixWord ++ tailWord_5666172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666172).length < 2 ^ (prefixWord ++ tailWord_5666172).sum := by decide
  have hdescent : baseEnd_5666172 < baseStart_5666172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666179 : List Nat := [1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 3]
def baseStart_5666179 : Nat := 118140960795 + 5666179 * 2 ^ 59
def prefixEnd_5666179 : Nat := 4983230072969 + 3 ^ 40 * 5666179 * 2
def baseEnd_5666179 : Nat := 2909473301412091782304223

theorem tailTrace_5666179 : CollatzResearch.WordTrace tailWord_5666179 prefixEnd_5666179 2909473301412091782304223 := by
  unfold tailWord_5666179
  simp only [CollatzResearch.WordTrace]
  refine ⟨206662526139408664175273591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137775017426272442783515727 206662526139408664175273591)
  ·
    refine ⟨309993789209112996262910387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206662526139408664175273591 309993789209112996262910387)
    ·
      refine ⟨464990683813669494394365581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309993789209112996262910387 464990683813669494394365581)
      ·
        refine ⟨174371506430126060397887093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 464990683813669494394365581 174371506430126060397887093)
        ·
          refine ⟨16347328727824318162301915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174371506430126060397887093 16347328727824318162301915)
          ·
            refine ⟨24520993091736477243452873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16347328727824318162301915 24520993091736477243452873)
            ·
              refine ⟨18390744818802357932589655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24520993091736477243452873 18390744818802357932589655)
              ·
                refine ⟨27586117228203536898884483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18390744818802357932589655 27586117228203536898884483)
                ·
                  refine ⟨41379175842305305348326725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27586117228203536898884483 41379175842305305348326725)
                  ·
                    refine ⟨7758595470432244752811261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41379175842305305348326725 7758595470432244752811261)
                    ·
                      refine ⟨2909473301412091782304223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7758595470432244752811261 2909473301412091782304223)
                      ·
                        rfl

theorem cell23_5666179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_5666179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666179 prefixEnd_5666179 := by exact prefixLift 5666179
  have htrace : WordTrace (prefixWord ++ tailWord_5666179) baseStart_5666179 baseEnd_5666179 := by
    simpa [prefixWord, tailWord_5666179, baseEnd_5666179] using wordTrace_append hprefix tailTrace_5666179
  have hstable : (prefixWord ++ tailWord_5666179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666179).length < 2 ^ (prefixWord ++ tailWord_5666179).sum := by decide
  have hdescent : baseEnd_5666179 < baseStart_5666179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666196 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_5666196 : Nat := 118140960795 + 5666196 * 2 ^ 59
def prefixEnd_5666196 : Nat := 4983230072969 + 3 ^ 40 * 5666196 * 2
def baseEnd_5666196 : Nat := 2909482030583218215791645

theorem tailTrace_5666196 : CollatzResearch.WordTrace tailWord_5666196 prefixEnd_5666196 2909482030583218215791645 := by
  unfold tailWord_5666196
  simp only [CollatzResearch.WordTrace]
  refine ⟨103331573090173538039321221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137775430786898050719094961 103331573090173538039321221)
  ·
    refine ⟨19374669954407538382372729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103331573090173538039321221 19374669954407538382372729)
    ·
      refine ⟨14531002465805653786779547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19374669954407538382372729 14531002465805653786779547)
      ·
        refine ⟨21796503698708480680169321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14531002465805653786779547 21796503698708480680169321)
        ·
          refine ⟨16347377774031360510126991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21796503698708480680169321 16347377774031360510126991)
          ·
            refine ⟨24521066661047040765190487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16347377774031360510126991 24521066661047040765190487)
            ·
              refine ⟨36781599991570561147785731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24521066661047040765190487 36781599991570561147785731)
              ·
                refine ⟨55172399987355841721678597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36781599991570561147785731 55172399987355841721678597)
                ·
                  refine ⟨10344824997629220322814737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55172399987355841721678597 10344824997629220322814737)
                  ·
                    refine ⟨7758618748221915242111053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10344824997629220322814737 7758618748221915242111053)
                    ·
                      refine ⟨2909482030583218215791645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7758618748221915242111053 2909482030583218215791645)
                      ·
                        rfl

theorem cell23_5666196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_5666196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666196 prefixEnd_5666196 := by exact prefixLift 5666196
  have htrace : WordTrace (prefixWord ++ tailWord_5666196) baseStart_5666196 baseEnd_5666196 := by
    simpa [prefixWord, tailWord_5666196, baseEnd_5666196] using wordTrace_append hprefix tailTrace_5666196
  have hstable : (prefixWord ++ tailWord_5666196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666196).length < 2 ^ (prefixWord ++ tailWord_5666196).sum := by decide
  have hdescent : baseEnd_5666196 < baseStart_5666196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666212 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 2, 9]
def baseStart_5666212 : Nat := 118140960795 + 5666212 * 2 ^ 59
def prefixEnd_5666212 : Nat := 4983230072969 + 3 ^ 40 * 5666212 * 2
def baseEnd_5666212 : Nat := 969830082091230051063857

theorem tailTrace_5666212 : CollatzResearch.WordTrace tailWord_5666212 prefixEnd_5666212 969830082091230051063857 := by
  unfold tailWord_5666212
  simp only [CollatzResearch.WordTrace]
  refine ⟨103331864874144555405612445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137775819832192740540816593 103331864874144555405612445)
  ·
    refine ⟨38749449327804208277104667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103331864874144555405612445 38749449327804208277104667)
    ·
      refine ⟨58124173991706312415657001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38749449327804208277104667 58124173991706312415657001)
      ·
        refine ⟨43593130493779734311742751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58124173991706312415657001 43593130493779734311742751)
        ·
          refine ⟨65389695740669601467614127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43593130493779734311742751 65389695740669601467614127)
          ·
            refine ⟨98084543611004402201421191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65389695740669601467614127 98084543611004402201421191)
            ·
              refine ⟨147126815416506603302131787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98084543611004402201421191 147126815416506603302131787)
              ·
                refine ⟨220690223124759904953197681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147126815416506603302131787 220690223124759904953197681)
                ·
                  refine ⟨165517667343569928714898261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220690223124759904953197681 165517667343569928714898261)
                  ·
                    refine ⟨969830082091230051063857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 165517667343569928714898261 969830082091230051063857)
                    ·
                      rfl

theorem cell23_5666212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_5666212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666212 prefixEnd_5666212 := by exact prefixLift 5666212
  have htrace : WordTrace (prefixWord ++ tailWord_5666212) baseStart_5666212 baseEnd_5666212 := by
    simpa [prefixWord, tailWord_5666212, baseEnd_5666212] using wordTrace_append hprefix tailTrace_5666212
  have hstable : (prefixWord ++ tailWord_5666212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666212).length < 2 ^ (prefixWord ++ tailWord_5666212).sum := by decide
  have hdescent : baseEnd_5666212 < baseStart_5666212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666272 : List Nat := [2, 1, 1, 3, 1, 1, 2, 12]
def baseStart_5666272 : Nat := 118140960795 + 5666272 * 2 ^ 59
def prefixEnd_5666272 : Nat := 4983230072969 + 3 ^ 40 * 5666272 * 2
def baseEnd_5666272 : Nat := 107760039078257774757085

theorem tailTrace_5666272 : CollatzResearch.WordTrace tailWord_5666272 prefixEnd_5666272 107760039078257774757085 := by
  unfold tailWord_5666272
  simp only [CollatzResearch.WordTrace]
  refine ⟨103332959064035870529204535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137777278752047827372272713 103332959064035870529204535)
  ·
    refine ⟨154999438596053805793806803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103332959064035870529204535 154999438596053805793806803)
    ·
      refine ⟨232499157894080708690710205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154999438596053805793806803 232499157894080708690710205)
      ·
        refine ⟨87187184210280265759016327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232499157894080708690710205 87187184210280265759016327)
        ·
          refine ⟨130780776315420398638524491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87187184210280265759016327 130780776315420398638524491)
          ·
            refine ⟨196171164473130597957786737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130780776315420398638524491 196171164473130597957786737)
            ·
              refine ⟨147128373354847948468340053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196171164473130597957786737 147128373354847948468340053)
              ·
                refine ⟨107760039078257774757085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 147128373354847948468340053 107760039078257774757085)
                ·
                  rfl

theorem cell23_5666272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 12].length) (baseStart_5666272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666272 prefixEnd_5666272 := by exact prefixLift 5666272
  have htrace : WordTrace (prefixWord ++ tailWord_5666272) baseStart_5666272 baseEnd_5666272 := by
    simpa [prefixWord, tailWord_5666272, baseEnd_5666272] using wordTrace_append hprefix tailTrace_5666272
  have hstable : (prefixWord ++ tailWord_5666272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666272).length < 2 ^ (prefixWord ++ tailWord_5666272).sum := by decide
  have hdescent : baseEnd_5666272 < baseStart_5666272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666286 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_5666286 : Nat := 118140960795 + 5666286 * 2 ^ 59
def prefixEnd_5666286 : Nat := 4983230072969 + 3 ^ 40 * 5666286 * 2
def baseEnd_5666286 : Nat := 2909528243842122863666231

theorem tailTrace_5666286 : CollatzResearch.WordTrace tailWord_5666286 prefixEnd_5666286 2909528243842122863666231 := by
  unfold tailWord_5666286
  simp only [CollatzResearch.WordTrace]
  refine ⟨25833303593752627681177339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137777619166680680966279141 25833303593752627681177339)
  ·
    refine ⟨38749955390628941521766009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25833303593752627681177339 38749955390628941521766009)
    ·
      refine ⟨29062466542971706141324507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38749955390628941521766009 29062466542971706141324507)
      ·
        refine ⟨43593699814457559211986761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29062466542971706141324507 43593699814457559211986761)
        ·
          refine ⟨32695274860843169408990071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43593699814457559211986761 32695274860843169408990071)
          ·
            refine ⟨49042912291264754113485107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32695274860843169408990071 49042912291264754113485107)
            ·
              refine ⟨73564368436897131170227661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49042912291264754113485107 73564368436897131170227661)
              ·
                refine ⟨27586638163836424188835373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73564368436897131170227661 27586638163836424188835373)
                ·
                  refine ⟨10344989311438659070813265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27586638163836424188835373 10344989311438659070813265)
                  ·
                    refine ⟨7758741983578994303109949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10344989311438659070813265 7758741983578994303109949)
                    ·
                      refine ⟨2909528243842122863666231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7758741983578994303109949 2909528243842122863666231)
                      ·
                        rfl

theorem cell23_5666286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_5666286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666286 prefixEnd_5666286 := by exact prefixLift 5666286
  have htrace : WordTrace (prefixWord ++ tailWord_5666286) baseStart_5666286 baseEnd_5666286 := by
    simpa [prefixWord, tailWord_5666286, baseEnd_5666286] using wordTrace_append hprefix tailTrace_5666286
  have hstable : (prefixWord ++ tailWord_5666286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666286).length < 2 ^ (prefixWord ++ tailWord_5666286).sum := by decide
  have hdescent : baseEnd_5666286 < baseStart_5666286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666300 : List Nat := [2, 2, 2, 1, 2, 1, 3, 5, 1, 2, 2]
def baseStart_5666300 : Nat := 118140960795 + 5666300 * 2 ^ 59
def prefixEnd_5666300 : Nat := 4983230072969 + 3 ^ 40 * 5666300 * 2
def baseEnd_5666300 : Nat := 2909535432571285808891167

theorem tailTrace_5666300 : CollatzResearch.WordTrace tailWord_5666300 prefixEnd_5666300 2909535432571285808891167 := by
  unfold tailWord_5666300
  simp only [CollatzResearch.WordTrace]
  refine ⟨103333469685985150920214177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137777959581313534560285569 103333469685985150920214177)
  ·
    refine ⟨77500102264488863190160633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103333469685985150920214177 77500102264488863190160633)
    ·
      refine ⟨58125076698366647392620475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77500102264488863190160633 58125076698366647392620475)
      ·
        refine ⟨87187615047549971088930713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58125076698366647392620475 87187615047549971088930713)
        ·
          refine ⟨65390711285662478316698035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87187615047549971088930713 65390711285662478316698035)
          ·
            refine ⟨98086066928493717475047053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65390711285662478316698035 98086066928493717475047053)
            ·
              refine ⟨36782275098185144053142645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98086066928493717475047053 36782275098185144053142645)
              ·
                refine ⟨3448338290454857254982123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36782275098185144053142645 3448338290454857254982123)
                ·
                  refine ⟨5172507435682285882473185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3448338290454857254982123 5172507435682285882473185)
                  ·
                    refine ⟨3879380576761714411854889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5172507435682285882473185 3879380576761714411854889)
                    ·
                      refine ⟨2909535432571285808891167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3879380576761714411854889 2909535432571285808891167)
                      ·
                        rfl

theorem cell23_5666300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_5666300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666300 prefixEnd_5666300 := by exact prefixLift 5666300
  have htrace : WordTrace (prefixWord ++ tailWord_5666300) baseStart_5666300 baseEnd_5666300 := by
    simpa [prefixWord, tailWord_5666300, baseEnd_5666300] using wordTrace_append hprefix tailTrace_5666300
  have hstable : (prefixWord ++ tailWord_5666300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666300).length < 2 ^ (prefixWord ++ tailWord_5666300).sum := by decide
  have hdescent : baseEnd_5666300 < baseStart_5666300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666306 : List Nat := [3, 4, 1, 2, 1, 2, 10]
def baseStart_5666306 : Nat := 118140960795 + 5666306 * 2 ^ 59
def prefixEnd_5666306 : Nat := 4983230072969 + 3 ^ 40 * 5666306 * 2
def baseEnd_5666306 : Nat := 35920228561175466486619

theorem tailTrace_5666306 : CollatzResearch.WordTrace tailWord_5666306 prefixEnd_5666306 35920228561175466486619 := by
  unfold tailWord_5666306
  simp only [CollatzResearch.WordTrace]
  refine ⟨51666789552487141216286693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137778105473299043243431181 51666789552487141216286693)
  ·
    refine ⟨9687523041091338978053755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51666789552487141216286693 9687523041091338978053755)
    ·
      refine ⟨14531284561637008467080633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9687523041091338978053755 14531284561637008467080633)
      ·
        refine ⟨10898463421227756350310475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14531284561637008467080633 10898463421227756350310475)
        ·
          refine ⟨16347695131841634525465713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10898463421227756350310475 16347695131841634525465713)
          ·
            refine ⟨12260771348881225894099285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16347695131841634525465713 12260771348881225894099285)
            ·
              refine ⟨35920228561175466486619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12260771348881225894099285 35920228561175466486619)
              ·
                rfl

theorem cell23_5666306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 10].length) (baseStart_5666306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666306 prefixEnd_5666306 := by exact prefixLift 5666306
  have htrace : WordTrace (prefixWord ++ tailWord_5666306) baseStart_5666306 baseEnd_5666306 := by
    simpa [prefixWord, tailWord_5666306, baseEnd_5666306] using wordTrace_append hprefix tailTrace_5666306
  have hstable : (prefixWord ++ tailWord_5666306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666306).length < 2 ^ (prefixWord ++ tailWord_5666306).sum := by decide
  have hdescent : baseEnd_5666306 < baseStart_5666306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666334 : List Nat := [4, 3, 3, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_5666334 : Nat := 118140960795 + 5666334 * 2 ^ 59
def prefixEnd_5666334 : Nat := 4983230072969 + 3 ^ 40 * 5666334 * 2
def baseEnd_5666334 : Nat := 2909552890913538675866011

theorem tailTrace_5666334 : CollatzResearch.WordTrace tailWord_5666334 prefixEnd_5666334 2909552890913538675866011 := by
  unfold tailWord_5666334
  simp only [CollatzResearch.WordTrace]
  refine ⟨25833522431730890705895757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137778786302564750431444037 25833522431730890705895757)
  ·
    refine ⟨9687570911899084014710909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25833522431730890705895757 9687570911899084014710909)
    ·
      refine ⟨3632839091962156505516591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9687570911899084014710909 3632839091962156505516591)
      ·
        refine ⟨5449258637943234758274887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3632839091962156505516591 5449258637943234758274887)
        ·
          refine ⟨8173887956914852137412331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5449258637943234758274887 8173887956914852137412331)
          ·
            refine ⟨12260831935372278206118497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8173887956914852137412331 12260831935372278206118497)
            ·
              refine ⟨9195623951529208654588873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12260831935372278206118497 9195623951529208654588873)
              ·
                refine ⟨6896717963646906490941655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9195623951529208654588873 6896717963646906490941655)
                ·
                  refine ⟨10345076945470359736412483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6896717963646906490941655 10345076945470359736412483)
                  ·
                    refine ⟨15517615418205539604618725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10345076945470359736412483 15517615418205539604618725)
                    ·
                      refine ⟨2909552890913538675866011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15517615418205539604618725 2909552890913538675866011)
                      ·
                        rfl

theorem cell23_5666334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_5666334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666334 prefixEnd_5666334 := by exact prefixLift 5666334
  have htrace : WordTrace (prefixWord ++ tailWord_5666334) baseStart_5666334 baseEnd_5666334 := by
    simpa [prefixWord, tailWord_5666334, baseEnd_5666334] using wordTrace_append hprefix tailTrace_5666334
  have hstable : (prefixWord ++ tailWord_5666334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666334).length < 2 ^ (prefixWord ++ tailWord_5666334).sum := by decide
  have hdescent : baseEnd_5666334 < baseStart_5666334 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666359 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 5]
def baseStart_5666359 : Nat := 118140960795 + 5666359 * 2 ^ 59
def prefixEnd_5666359 : Nat := 4983230072969 + 3 ^ 40 * 5666359 * 2
def baseEnd_5666359 : Nat := 2909565727929901078053395

theorem tailTrace_5666359 : CollatzResearch.WordTrace tailWord_5666359 prefixEnd_5666359 2909565727929901078053395 := by
  unfold tailWord_5666359
  simp only [CollatzResearch.WordTrace]
  refine ⟨206669091278756554916826131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137779394185837703277884087 206669091278756554916826131)
  ·
    refine ⟨310003636918134832375239197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206669091278756554916826131 310003636918134832375239197)
    ·
      refine ⟨116251363844300562140714699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310003636918134832375239197 116251363844300562140714699)
      ·
        refine ⟨174377045766450843211072049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116251363844300562140714699 174377045766450843211072049)
        ·
          refine ⟨130782784324838132408304037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174377045766450843211072049 130782784324838132408304037)
          ·
            refine ⟨24521772060907149826557007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130782784324838132408304037 24521772060907149826557007)
            ·
              refine ⟨36782658091360724739835511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24521772060907149826557007 36782658091360724739835511)
              ·
                refine ⟨55173987137041087109753267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36782658091360724739835511 55173987137041087109753267)
                ·
                  refine ⟨82760980705561630664629901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55173987137041087109753267 82760980705561630664629901)
                  ·
                    refine ⟨31035367764585611499236213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82760980705561630664629901 31035367764585611499236213)
                    ·
                      refine ⟨2909565727929901078053395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31035367764585611499236213 2909565727929901078053395)
                      ·
                        rfl

theorem cell23_5666359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_5666359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666359 prefixEnd_5666359 := by exact prefixLift 5666359
  have htrace : WordTrace (prefixWord ++ tailWord_5666359) baseStart_5666359 baseEnd_5666359 := by
    simpa [prefixWord, tailWord_5666359, baseEnd_5666359] using wordTrace_append hprefix tailTrace_5666359
  have hstable : (prefixWord ++ tailWord_5666359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666359).length < 2 ^ (prefixWord ++ tailWord_5666359).sum := by decide
  have hdescent : baseEnd_5666359 < baseStart_5666359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666373 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 4, 2, 2]
def baseStart_5666373 : Nat := 118140960795 + 5666373 * 2 ^ 59
def prefixEnd_5666373 : Nat := 4983230072969 + 3 ^ 40 * 5666373 * 2
def baseEnd_5666373 : Nat := 2909572916659064023278331

theorem tailTrace_5666373 : CollatzResearch.WordTrace tailWord_5666373 prefixEnd_5666373 2909572916659064023278331 := by
  unfold tailWord_5666373
  simp only [CollatzResearch.WordTrace]
  refine ⟨206669601900705835307835773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137779734600470556871890515 206669601900705835307835773)
  ·
    refine ⟨77501100712764688240438415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206669601900705835307835773 77501100712764688240438415)
    ·
      refine ⟨116251651069147032360657623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77501100712764688240438415 116251651069147032360657623)
      ·
        refine ⟨174377476603720548540986435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116251651069147032360657623 174377476603720548540986435)
        ·
          refine ⟨261566214905580822811479653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174377476603720548540986435 261566214905580822811479653)
          ·
            refine ⟨49043665294796404277152435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 261566214905580822811479653 49043665294796404277152435)
            ·
              refine ⟨73565497942194606415728653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49043665294796404277152435 73565497942194606415728653)
              ·
                refine ⟨27587061728322977405898245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73565497942194606415728653 27587061728322977405898245)
                ·
                  refine ⟨5172574074060558263605921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27587061728322977405898245 5172574074060558263605921)
                  ·
                    refine ⟨3879430555545418697704441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5172574074060558263605921 3879430555545418697704441)
                    ·
                      refine ⟨2909572916659064023278331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3879430555545418697704441 2909572916659064023278331)
                      ·
                        rfl

theorem cell23_5666373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 4, 2, 2].length) (baseStart_5666373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666373 prefixEnd_5666373 := by exact prefixLift 5666373
  have htrace : WordTrace (prefixWord ++ tailWord_5666373) baseStart_5666373 baseEnd_5666373 := by
    simpa [prefixWord, tailWord_5666373, baseEnd_5666373] using wordTrace_append hprefix tailTrace_5666373
  have hstable : (prefixWord ++ tailWord_5666373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666373).length < 2 ^ (prefixWord ++ tailWord_5666373).sum := by decide
  have hdescent : baseEnd_5666373 < baseStart_5666373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666409 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 1, 7]
def baseStart_5666409 : Nat := 118140960795 + 5666409 * 2 ^ 59
def prefixEnd_5666409 : Nat := 4983230072969 + 3 ^ 40 * 5666409 * 2
def baseEnd_5666409 : Nat := 969863800654208627476055

theorem tailTrace_5666409 : CollatzResearch.WordTrace tailWord_5666409 prefixEnd_5666409 969863800654208627476055 := by
  unfold tailWord_5666409
  simp only [CollatzResearch.WordTrace]
  refine ⟨206670914928575413456146281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137780609952383608970764187 206670914928575413456146281)
  ·
    refine ⟨155003186196431560092109711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206670914928575413456146281 155003186196431560092109711)
    ·
      refine ⟨232504779294647340138164567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155003186196431560092109711 232504779294647340138164567)
      ·
        refine ⟨348757168941971010207246851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232504779294647340138164567 348757168941971010207246851)
        ·
          refine ⟨523135753412956515310870277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348757168941971010207246851 523135753412956515310870277)
          ·
            refine ⟨98087953764929346620788177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 523135753412956515310870277 98087953764929346620788177)
            ·
              refine ⟨73565965323697009965591133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98087953764929346620788177 73565965323697009965591133)
              ·
                refine ⟨27587236996386378737096675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73565965323697009965591133 27587236996386378737096675)
                ·
                  refine ⟨41380855494579568105645013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27587236996386378737096675 41380855494579568105645013)
                  ·
                    refine ⟨969863800654208627476055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41380855494579568105645013 969863800654208627476055)
                    ·
                      rfl

theorem cell23_5666409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 1, 7].length) (baseStart_5666409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666409 prefixEnd_5666409 := by exact prefixLift 5666409
  have htrace : WordTrace (prefixWord ++ tailWord_5666409) baseStart_5666409 baseEnd_5666409 := by
    simpa [prefixWord, tailWord_5666409, baseEnd_5666409] using wordTrace_append hprefix tailTrace_5666409
  have hstable : (prefixWord ++ tailWord_5666409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666409).length < 2 ^ (prefixWord ++ tailWord_5666409).sum := by decide
  have hdescent : baseEnd_5666409 < baseStart_5666409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666433 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 2, 5, 2]
def baseStart_5666433 : Nat := 118140960795 + 5666433 * 2 ^ 59
def prefixEnd_5666433 : Nat := 4983230072969 + 3 ^ 40 * 5666433 * 2
def baseEnd_5666433 : Nat := 2909603725498333788528055

theorem tailTrace_5666433 : CollatzResearch.WordTrace tailWord_5666433 prefixEnd_5666433 2909603725498333788528055 := by
  unfold tailWord_5666433
  simp only [CollatzResearch.WordTrace]
  refine ⟨206671790280488465555019953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137781193520325643703346635 206671790280488465555019953)
  ·
    refine ⟨155003842710366349166264965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206671790280488465555019953 155003842710366349166264965)
    ·
      refine ⟨29063220508193690468674681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155003842710366349166264965 29063220508193690468674681)
      ·
        refine ⟨21797415381145267851506011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29063220508193690468674681 21797415381145267851506011)
        ·
          refine ⟨32696123071717901777259017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21797415381145267851506011 32696123071717901777259017)
          ·
            refine ⟨24522092303788426332944263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32696123071717901777259017 24522092303788426332944263)
            ·
              refine ⟨36783138455682639499416395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24522092303788426332944263 36783138455682639499416395)
              ·
                refine ⟨55174707683523959249124593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36783138455682639499416395 55174707683523959249124593)
                ·
                  refine ⟨41381030762642969436843445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55174707683523959249124593 41381030762642969436843445)
                  ·
                    refine ⟨3879471633997778384704073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41381030762642969436843445 3879471633997778384704073)
                    ·
                      refine ⟨2909603725498333788528055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3879471633997778384704073 2909603725498333788528055)
                      ·
                        rfl

theorem cell23_5666433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_5666433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666433 prefixEnd_5666433 := by exact prefixLift 5666433
  have htrace : WordTrace (prefixWord ++ tailWord_5666433) baseStart_5666433 baseEnd_5666433 := by
    simpa [prefixWord, tailWord_5666433, baseEnd_5666433] using wordTrace_append hprefix tailTrace_5666433
  have hstable : (prefixWord ++ tailWord_5666433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666433).length < 2 ^ (prefixWord ++ tailWord_5666433).sum := by decide
  have hdescent : baseEnd_5666433 < baseStart_5666433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666440 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5666440 : Nat := 118140960795 + 5666440 * 2 ^ 59
def prefixEnd_5666440 : Nat := 4983230072969 + 3 ^ 40 * 5666440 * 2
def baseEnd_5666440 : Nat := 2909607319862915261140523

theorem tailTrace_5666440 : CollatzResearch.WordTrace tailWord_5666440 prefixEnd_5666440 2909607319862915261140523 := by
  unfold tailWord_5666440
  simp only [CollatzResearch.WordTrace]
  refine ⟨103336022795731552875262387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137781363727642070500349849 103336022795731552875262387)
  ·
    refine ⟨155004034193597329312893581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103336022795731552875262387 155004034193597329312893581)
    ·
      refine ⟨58126512822598998492335093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155004034193597329312893581 58126512822598998492335093)
      ·
        refine ⟨5449360577118656108656415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58126512822598998492335093 5449360577118656108656415)
        ·
          refine ⟨8174040865677984162984623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5449360577118656108656415 8174040865677984162984623)
          ·
            refine ⟨12261061298516976244476935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8174040865677984162984623 12261061298516976244476935)
            ·
              refine ⟨18391591947775464366715403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12261061298516976244476935 18391591947775464366715403)
              ·
                refine ⟨27587387921663196550073105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18391591947775464366715403 27587387921663196550073105)
                ·
                  refine ⟨20690540941247397412554829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27587387921663196550073105 20690540941247397412554829)
                  ·
                    refine ⟨7758952852967774029708061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20690540941247397412554829 7758952852967774029708061)
                    ·
                      refine ⟨2909607319862915261140523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7758952852967774029708061 2909607319862915261140523)
                      ·
                        rfl

theorem cell23_5666440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5666440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666440 prefixEnd_5666440 := by exact prefixLift 5666440
  have htrace : WordTrace (prefixWord ++ tailWord_5666440) baseStart_5666440 baseEnd_5666440 := by
    simpa [prefixWord, tailWord_5666440, baseEnd_5666440] using wordTrace_append hprefix tailTrace_5666440
  have hstable : (prefixWord ++ tailWord_5666440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666440).length < 2 ^ (prefixWord ++ tailWord_5666440).sum := by decide
  have hdescent : baseEnd_5666440 < baseStart_5666440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666460 : List Nat := [2, 2, 3, 2, 3, 2, 1, 1, 2, 5]
def baseStart_5666460 : Nat := 118140960795 + 5666460 * 2 ^ 59
def prefixEnd_5666460 : Nat := 4983230072969 + 3 ^ 40 * 5666460 * 2
def baseEnd_5666460 : Nat := 969872529825335060963477

theorem tailTrace_5666460 : CollatzResearch.WordTrace tailWord_5666460 prefixEnd_5666460 969872529825335060963477 := by
  unfold tailWord_5666460
  simp only [CollatzResearch.WordTrace]
  refine ⟨103336387525695324583126417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137781850034260432777501889 103336387525695324583126417)
  ·
    refine ⟨77502290644271493437344813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103336387525695324583126417 77502290644271493437344813)
    ·
      refine ⟨29063358991601810039004305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77502290644271493437344813 29063358991601810039004305)
      ·
        refine ⟨21797519243701357529253229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29063358991601810039004305 21797519243701357529253229)
        ·
          refine ⟨8174069716388009073469961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21797519243701357529253229 8174069716388009073469961)
          ·
            refine ⟨6130552287291006805102471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8174069716388009073469961 6130552287291006805102471)
            ·
              refine ⟨9195828430936510207653707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6130552287291006805102471 9195828430936510207653707)
              ·
                refine ⟨13793742646404765311480561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9195828430936510207653707 13793742646404765311480561)
                ·
                  refine ⟨10345306984803573983610421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13793742646404765311480561 10345306984803573983610421)
                  ·
                    refine ⟨969872529825335060963477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10345306984803573983610421 969872529825335060963477)
                    ·
                      rfl

theorem cell23_5666460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_5666460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666460 prefixEnd_5666460 := by exact prefixLift 5666460
  have htrace : WordTrace (prefixWord ++ tailWord_5666460) baseStart_5666460 baseEnd_5666460 := by
    simpa [prefixWord, tailWord_5666460, baseEnd_5666460] using wordTrace_append hprefix tailTrace_5666460
  have hstable : (prefixWord ++ tailWord_5666460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666460).length < 2 ^ (prefixWord ++ tailWord_5666460).sum := by decide
  have hdescent : baseEnd_5666460 < baseStart_5666460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666490 : List Nat := [3, 1, 1, 1, 2, 4, 2, 4, 1, 4]
def baseStart_5666490 : Nat := 118140960795 + 5666490 * 2 ^ 59
def prefixEnd_5666490 : Nat := 4983230072969 + 3 ^ 40 * 5666490 * 2
def baseEnd_5666490 : Nat := 969877664631880021838431

theorem tailTrace_5666490 : CollatzResearch.WordTrace tailWord_5666490 prefixEnd_5666490 969877664631880021838431 := by
  unfold tailWord_5666490
  simp only [CollatzResearch.WordTrace]
  refine ⟨51668467310320491072461231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137782579494187976193229949 51668467310320491072461231)
  ·
    refine ⟨77502700965480736608691847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51668467310320491072461231 77502700965480736608691847)
    ·
      refine ⟨116254051448221104913037771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77502700965480736608691847 116254051448221104913037771)
      ·
        refine ⟨174381077172331657369556657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116254051448221104913037771 174381077172331657369556657)
        ·
          refine ⟨130785807879248743027167493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174381077172331657369556657 130785807879248743027167493)
          ·
            refine ⟨24522338977359139317593905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130785807879248743027167493 24522338977359139317593905)
            ·
              refine ⟨18391754233019354488195429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24522338977359139317593905 18391754233019354488195429)
              ·
                refine ⟨3448453918691128966536643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18391754233019354488195429 3448453918691128966536643)
                ·
                  refine ⟨5172680878036693449804965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3448453918691128966536643 5172680878036693449804965)
                  ·
                    refine ⟨969877664631880021838431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5172680878036693449804965 969877664631880021838431)
                    ·
                      rfl

theorem cell23_5666490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 1, 4].length) (baseStart_5666490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666490 prefixEnd_5666490 := by exact prefixLift 5666490
  have htrace : WordTrace (prefixWord ++ tailWord_5666490) baseStart_5666490 baseEnd_5666490 := by
    simpa [prefixWord, tailWord_5666490, baseEnd_5666490] using wordTrace_append hprefix tailTrace_5666490
  have hstable : (prefixWord ++ tailWord_5666490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666490).length < 2 ^ (prefixWord ++ tailWord_5666490).sum := by decide
  have hdescent : baseEnd_5666490 < baseStart_5666490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666503 : List Nat := [1, 1, 4, 1, 1, 1, 7, 1, 6]
def baseStart_5666503 : Nat := 118140960795 + 5666503 * 2 ^ 59
def prefixEnd_5666503 : Nat := 4983230072969 + 3 ^ 40 * 5666503 * 2
def baseEnd_5666503 : Nat := 323293296571572057183637

theorem tailTrace_5666503 : CollatzResearch.WordTrace tailWord_5666503 prefixEnd_5666503 323293296571572057183637 := by
  unfold tailWord_5666503
  simp only [CollatzResearch.WordTrace]
  refine ⟨206674343390234867510068163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137782895593489911673378775 206674343390234867510068163)
  ·
    refine ⟨310011515085352301265102245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206674343390234867510068163 310011515085352301265102245)
    ·
      refine ⟨58127159078503556487206671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310011515085352301265102245 58127159078503556487206671)
      ·
        refine ⟨87190738617755334730810007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58127159078503556487206671 87190738617755334730810007)
        ·
          refine ⟨130786107926633002096215011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87190738617755334730810007 130786107926633002096215011)
          ·
            refine ⟨196179161889949503144322517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130786107926633002096215011 196179161889949503144322517)
            ·
              refine ⟨4597949106795691479945059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 196179161889949503144322517 4597949106795691479945059)
              ·
                refine ⟨6896923660193537219917589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4597949106795691479945059 6896923660193537219917589)
                ·
                  refine ⟨323293296571572057183637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6896923660193537219917589 323293296571572057183637)
                  ·
                    rfl

theorem cell23_5666503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 7, 1, 6].length) (baseStart_5666503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666503 prefixEnd_5666503 := by exact prefixLift 5666503
  have htrace : WordTrace (prefixWord ++ tailWord_5666503) baseStart_5666503 baseEnd_5666503 := by
    simpa [prefixWord, tailWord_5666503, baseEnd_5666503] using wordTrace_append hprefix tailTrace_5666503
  have hstable : (prefixWord ++ tailWord_5666503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666503).length < 2 ^ (prefixWord ++ tailWord_5666503).sum := by decide
  have hdescent : baseEnd_5666503 < baseStart_5666503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666533 : List Nat := [1, 3, 1, 4, 1, 1, 1, 5, 1, 5]
def baseStart_5666533 : Nat := 118140960795 + 5666533 * 2 ^ 59
def prefixEnd_5666533 : Nat := 4983230072969 + 3 ^ 40 * 5666533 * 2
def baseEnd_5666533 : Nat := 969885024521261132425865

theorem tailTrace_5666533 : CollatzResearch.WordTrace tailWord_5666533 prefixEnd_5666533 969885024521261132425865 := by
  unfold tailWord_5666533
  simp only [CollatzResearch.WordTrace]
  refine ⟨206675437580126182633660253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137783625053417455089106835 206675437580126182633660253)
  ·
    refine ⟨77503289092547318487622595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206675437580126182633660253 77503289092547318487622595)
    ·
      refine ⟨116254933638820977731433893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77503289092547318487622595 116254933638820977731433893)
      ·
        refine ⟨21797800057278933324643855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116254933638820977731433893 21797800057278933324643855)
        ·
          refine ⟨32696700085918399986965783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21797800057278933324643855 32696700085918399986965783)
          ·
            refine ⟨49045050128877599980448675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32696700085918399986965783 49045050128877599980448675)
            ·
              refine ⟨73567575193316399970673013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49045050128877599980448675 73567575193316399970673013)
              ·
                refine ⟨6896960174373412497250595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73567575193316399970673013 6896960174373412497250595)
                ·
                  refine ⟨10345440261560118745875893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6896960174373412497250595 10345440261560118745875893)
                  ·
                    refine ⟨969885024521261132425865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10345440261560118745875893 969885024521261132425865)
                    ·
                      rfl

theorem cell23_5666533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_5666533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666533 prefixEnd_5666533 := by exact prefixLift 5666533
  have htrace : WordTrace (prefixWord ++ tailWord_5666533) baseStart_5666533 baseEnd_5666533 := by
    simpa [prefixWord, tailWord_5666533, baseEnd_5666533] using wordTrace_append hprefix tailTrace_5666533
  have hstable : (prefixWord ++ tailWord_5666533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666533).length < 2 ^ (prefixWord ++ tailWord_5666533).sum := by decide
  have hdescent : baseEnd_5666533 < baseStart_5666533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666567 : List Nat := [1, 1, 4, 4, 2, 2, 1, 2, 1, 5]
def baseStart_5666567 : Nat := 118140960795 + 5666567 * 2 ^ 59
def prefixEnd_5666567 : Nat := 4983230072969 + 3 ^ 40 * 5666567 * 2
def baseEnd_5666567 : Nat := 969890843968678754750813

theorem tailTrace_5666567 : CollatzResearch.WordTrace tailWord_5666567 prefixEnd_5666567 969890843968678754750813 := by
  unfold tailWord_5666567
  simp only [CollatzResearch.WordTrace]
  refine ⟨206676677662003006440397955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137784451774668670960265303 206676677662003006440397955)
  ·
    refine ⟨310015016493004509660596933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206676677662003006440397955 310015016493004509660596933)
    ·
      refine ⟨58127815592438345561361925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310015016493004509660596933 58127815592438345561361925)
      ·
        refine ⟨10898965423582189792755361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58127815592438345561361925 10898965423582189792755361)
        ·
          refine ⟨8174224067686642344566521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10898965423582189792755361 8174224067686642344566521)
          ·
            refine ⟨6130668050764981758424891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8174224067686642344566521 6130668050764981758424891)
            ·
              refine ⟨9196002076147472637637337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6130668050764981758424891 9196002076147472637637337)
              ·
                refine ⟨6897001557110604478228003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9196002076147472637637337 6897001557110604478228003)
                ·
                  refine ⟨10345502335665906717342005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6897001557110604478228003 10345502335665906717342005)
                  ·
                    refine ⟨969890843968678754750813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10345502335665906717342005 969890843968678754750813)
                    ·
                      rfl

theorem cell23_5666567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_5666567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666567 prefixEnd_5666567 := by exact prefixLift 5666567
  have htrace : WordTrace (prefixWord ++ tailWord_5666567) baseStart_5666567 baseEnd_5666567 := by
    simpa [prefixWord, tailWord_5666567, baseEnd_5666567] using wordTrace_append hprefix tailTrace_5666567
  have hstable : (prefixWord ++ tailWord_5666567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666567).length < 2 ^ (prefixWord ++ tailWord_5666567).sum := by decide
  have hdescent : baseEnd_5666567 < baseStart_5666567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666570 : List Nat := [3, 1, 2, 2, 1, 3, 3, 2, 1, 1, 4]
def baseStart_5666570 : Nat := 118140960795 + 5666570 * 2 ^ 59
def prefixEnd_5666570 : Nat := 4983230072969 + 3 ^ 40 * 5666570 * 2
def baseEnd_5666570 : Nat := 2909674072347999752514925

theorem tailTrace_5666570 : CollatzResearch.WordTrace tailWord_5666570 prefixEnd_5666570 2909674072347999752514925 := by
  unfold tailWord_5666570
  simp only [CollatzResearch.WordTrace]
  refine ⟨51669196770248034488189291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137784524720661425301838109 51669196770248034488189291)
  ·
    refine ⟨77503795155372051732283937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51669196770248034488189291 77503795155372051732283937)
    ·
      refine ⟨58127846366529038799212953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77503795155372051732283937 58127846366529038799212953)
      ·
        refine ⟨43595884774896779099409715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58127846366529038799212953 43595884774896779099409715)
        ·
          refine ⟨65393827162345168649114573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43595884774896779099409715 65393827162345168649114573)
          ·
            refine ⟨24522685185879438243417965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65393827162345168649114573 24522685185879438243417965)
            ·
              refine ⟨9196006944704789341281737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24522685185879438243417965 9196006944704789341281737)
              ·
                refine ⟨6897005208528592005961303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9196006944704789341281737 6897005208528592005961303)
                ·
                  refine ⟨10345507812792888008941955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6897005208528592005961303 10345507812792888008941955)
                  ·
                    refine ⟨15518261719189332013412933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10345507812792888008941955 15518261719189332013412933)
                    ·
                      refine ⟨2909674072347999752514925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15518261719189332013412933 2909674072347999752514925)
                      ·
                        rfl

theorem cell23_5666570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_5666570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666570 prefixEnd_5666570 := by exact prefixLift 5666570
  have htrace : WordTrace (prefixWord ++ tailWord_5666570) baseStart_5666570 baseEnd_5666570 := by
    simpa [prefixWord, tailWord_5666570, baseEnd_5666570] using wordTrace_append hprefix tailTrace_5666570
  have hstable : (prefixWord ++ tailWord_5666570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666570).length < 2 ^ (prefixWord ++ tailWord_5666570).sum := by decide
  have hdescent : baseEnd_5666570 < baseStart_5666570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666583 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 4]
def baseStart_5666583 : Nat := 118140960795 + 5666583 * 2 ^ 59
def prefixEnd_5666583 : Nat := 4983230072969 + 3 ^ 40 * 5666583 * 2
def baseEnd_5666583 : Nat := 2909680747596508201652365

theorem tailTrace_5666583 : CollatzResearch.WordTrace tailWord_5666583 prefixEnd_5666583 2909680747596508201652365 := by
  unfold tailWord_5666583
  simp only [CollatzResearch.WordTrace]
  refine ⟨206677261229945041172980403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137784840819963360781986935 206677261229945041172980403)
  ·
    refine ⟨310015891844917561759470605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206677261229945041172980403 310015891844917561759470605)
    ·
      refine ⟨116255959441844085659801477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310015891844917561759470605 116255959441844085659801477)
      ·
        refine ⟨21797992395345766061212777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116255959441844085659801477 21797992395345766061212777)
        ·
          refine ⟨16348494296509324545909583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21797992395345766061212777 16348494296509324545909583)
          ·
            refine ⟨24522741444763986818864375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16348494296509324545909583 24522741444763986818864375)
            ·
              refine ⟨36784112167145980228296563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24522741444763986818864375 36784112167145980228296563)
              ·
                refine ⟨55176168250718970342444845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36784112167145980228296563 55176168250718970342444845)
                ·
                  refine ⟨20691063094019613878416817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55176168250718970342444845 20691063094019613878416817)
                  ·
                    refine ⟨15518297320514710408812613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20691063094019613878416817 15518297320514710408812613)
                    ·
                      refine ⟨2909680747596508201652365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15518297320514710408812613 2909680747596508201652365)
                      ·
                        rfl

theorem cell23_5666583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_5666583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666583 prefixEnd_5666583 := by exact prefixLift 5666583
  have htrace : WordTrace (prefixWord ++ tailWord_5666583) baseStart_5666583 baseEnd_5666583 := by
    simpa [prefixWord, tailWord_5666583, baseEnd_5666583] using wordTrace_append hprefix tailTrace_5666583
  have hstable : (prefixWord ++ tailWord_5666583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666583).length < 2 ^ (prefixWord ++ tailWord_5666583).sum := by decide
  have hdescent : baseEnd_5666583 < baseStart_5666583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666604 : List Nat := [2, 2, 1, 1, 1, 6, 1, 4, 1, 2, 2]
def baseStart_5666604 : Nat := 118140960795 + 5666604 * 2 ^ 59
def prefixEnd_5666604 : Nat := 4983230072969 + 3 ^ 40 * 5666604 * 2
def baseEnd_5666604 : Nat := 2909691530690252619489769

theorem tailTrace_5666604 : CollatzResearch.WordTrace tailWord_5666604 prefixEnd_5666604 2909691530690252619489769 := by
  unfold tailWord_5666604
  simp only [CollatzResearch.WordTrace]
  refine ⟨103339013581434480879747433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137785351441912641172996577 103339013581434480879747433)
  ·
    refine ⟨77504260186075860659810575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103339013581434480879747433 77504260186075860659810575)
    ·
      refine ⟨116256390279113790989715863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77504260186075860659810575 116256390279113790989715863)
      ·
        refine ⟨174384585418670686484573795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116256390279113790989715863 174384585418670686484573795)
        ·
          refine ⟨261576878128006029726860693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174384585418670686484573795 261576878128006029726860693)
          ·
            refine ⟨12261416162250282643446595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 261576878128006029726860693 12261416162250282643446595)
            ·
              refine ⟨18392124243375423965169893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12261416162250282643446595 18392124243375423965169893)
              ·
                refine ⟨3448523295632891993469355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18392124243375423965169893 3448523295632891993469355)
                ·
                  refine ⟨5172784943449337990204033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3448523295632891993469355 5172784943449337990204033)
                  ·
                    refine ⟨3879588707587003492653025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5172784943449337990204033 3879588707587003492653025)
                    ·
                      refine ⟨2909691530690252619489769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3879588707587003492653025 2909691530690252619489769)
                      ·
                        rfl

theorem cell23_5666604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 1, 2, 2].length) (baseStart_5666604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666604 prefixEnd_5666604 := by exact prefixLift 5666604
  have htrace : WordTrace (prefixWord ++ tailWord_5666604) baseStart_5666604 baseEnd_5666604 := by
    simpa [prefixWord, tailWord_5666604, baseEnd_5666604] using wordTrace_append hprefix tailTrace_5666604
  have hstable : (prefixWord ++ tailWord_5666604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666604).length < 2 ^ (prefixWord ++ tailWord_5666604).sum := by decide
  have hdescent : baseEnd_5666604 < baseStart_5666604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666617 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 1, 2, 4]
def baseStart_5666617 : Nat := 118140960795 + 5666617 * 2 ^ 59
def prefixEnd_5666617 : Nat := 4983230072969 + 3 ^ 40 * 5666617 * 2
def baseEnd_5666617 : Nat := 2909698205938761068627209

theorem tailTrace_5666617 : CollatzResearch.WordTrace tailWord_5666617 prefixEnd_5666617 2909698205938761068627209 := by
  unfold tailWord_5666617
  simp only [CollatzResearch.WordTrace]
  refine ⟨206678501311821864979718105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137785667541214576653145403 206678501311821864979718105)
  ·
    refine ⟨155008875983866398734788579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206678501311821864979718105 155008875983866398734788579)
    ·
      refine ⟨232513313975799598102182869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155008875983866398734788579 232513313975799598102182869)
      ·
        refine ⟨5449530796307803080519911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 232513313975799598102182869 5449530796307803080519911)
        ·
          refine ⟨8174296194461704620779867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5449530796307803080519911 8174296194461704620779867)
          ·
            refine ⟨12261444291692556931169801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8174296194461704620779867 12261444291692556931169801)
            ·
              refine ⟨9196083218769417698377351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12261444291692556931169801 9196083218769417698377351)
              ·
                refine ⟨13794124828154126547566027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9196083218769417698377351 13794124828154126547566027)
                ·
                  refine ⟨20691187242231189821349041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13794124828154126547566027 20691187242231189821349041)
                  ·
                    refine ⟨15518390431673392366011781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20691187242231189821349041 15518390431673392366011781)
                    ·
                      refine ⟨2909698205938761068627209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15518390431673392366011781 2909698205938761068627209)
                      ·
                        rfl

theorem cell23_5666617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_5666617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666617 prefixEnd_5666617 := by exact prefixLift 5666617
  have htrace : WordTrace (prefixWord ++ tailWord_5666617) baseStart_5666617 baseEnd_5666617 := by
    simpa [prefixWord, tailWord_5666617, baseEnd_5666617] using wordTrace_append hprefix tailTrace_5666617
  have hstable : (prefixWord ++ tailWord_5666617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666617).length < 2 ^ (prefixWord ++ tailWord_5666617).sum := by decide
  have hdescent : baseEnd_5666617 < baseStart_5666617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666637 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_5666637 : Nat := 118140960795 + 5666637 * 2 ^ 59
def prefixEnd_5666637 : Nat := 4983230072969 + 3 ^ 40 * 5666637 * 2
def baseEnd_5666637 : Nat := 2909708475551850990377117

theorem tailTrace_5666637 : CollatzResearch.WordTrace tailWord_5666637 prefixEnd_5666637 2909708475551850990377117 := by
  unfold tailWord_5666637
  simp only [CollatzResearch.WordTrace]
  refine ⟨206679230771749408395446165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137786153847832938930297443 206679230771749408395446165)
  ·
    refine ⟨9688088942425753518536539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 206679230771749408395446165 9688088942425753518536539)
    ·
      refine ⟨14532133413638630277804809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9688088942425753518536539 14532133413638630277804809)
      ·
        refine ⟨10899100060228972708353607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14532133413638630277804809 10899100060228972708353607)
        ·
          refine ⟨16348650090343459062530411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10899100060228972708353607 16348650090343459062530411)
          ·
            refine ⟨24522975135515188593795617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16348650090343459062530411 24522975135515188593795617)
            ·
              refine ⟨18392231351636391445346713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24522975135515188593795617 18392231351636391445346713)
              ·
                refine ⟨13794173513727293584010035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18392231351636391445346713 13794173513727293584010035)
                ·
                  refine ⟨20691260270590940376015053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13794173513727293584010035 20691260270590940376015053)
                  ·
                    refine ⟨7759222601471602641005645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20691260270590940376015053 7759222601471602641005645)
                    ·
                      refine ⟨2909708475551850990377117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7759222601471602641005645 2909708475551850990377117)
                      ·
                        rfl

theorem cell23_5666637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_5666637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666637 prefixEnd_5666637 := by exact prefixLift 5666637
  have htrace : WordTrace (prefixWord ++ tailWord_5666637) baseStart_5666637 baseEnd_5666637 := by
    simpa [prefixWord, tailWord_5666637, baseEnd_5666637] using wordTrace_append hprefix tailTrace_5666637
  have hstable : (prefixWord ++ tailWord_5666637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666637).length < 2 ^ (prefixWord ++ tailWord_5666637).sum := by decide
  have hdescent : baseEnd_5666637 < baseStart_5666637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666670 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 2, 6]
def baseStart_5666670 : Nat := 118140960795 + 5666670 * 2 ^ 59
def prefixEnd_5666670 : Nat := 4983230072969 + 3 ^ 40 * 5666670 * 2
def baseEnd_5666670 : Nat := 969908473471149787088155

theorem tailTrace_5666670 : CollatzResearch.WordTrace tailWord_5666670 prefixEnd_5666670 969908473471149787088155 := by
  unfold tailWord_5666670
  simp only [CollatzResearch.WordTrace]
  refine ⟨25835054297578731878924683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137786956253753236687598309 25835054297578731878924683)
  ·
    refine ⟨38752581446368097818387025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25835054297578731878924683 38752581446368097818387025)
    ·
      refine ⟨29064436084776073363790269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38752581446368097818387025 29064436084776073363790269)
      ·
        refine ⟨10899163531791027511421351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29064436084776073363790269 10899163531791027511421351)
        ·
          refine ⟨16348745297686541267132027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10899163531791027511421351 16348745297686541267132027)
          ·
            refine ⟨24523117946529811900698041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16348745297686541267132027 24523117946529811900698041)
            ·
              refine ⟨18392338459897358925523531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24523117946529811900698041 18392338459897358925523531)
              ·
                refine ⟨27588507689846038388285297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18392338459897358925523531 27588507689846038388285297)
                ·
                  refine ⟨20691380767384528791213973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27588507689846038388285297 20691380767384528791213973)
                  ·
                    refine ⟨969908473471149787088155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20691380767384528791213973 969908473471149787088155)
                    ·
                      rfl

theorem cell23_5666670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_5666670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666670 prefixEnd_5666670 := by exact prefixLift 5666670
  have htrace : WordTrace (prefixWord ++ tailWord_5666670) baseStart_5666670 baseEnd_5666670 := by
    simpa [prefixWord, tailWord_5666670, baseEnd_5666670] using wordTrace_append hprefix tailTrace_5666670
  have hstable : (prefixWord ++ tailWord_5666670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666670).length < 2 ^ (prefixWord ++ tailWord_5666670).sum := by decide
  have hdescent : baseEnd_5666670 < baseStart_5666670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666673 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 2, 2, 4]
def baseStart_5666673 : Nat := 118140960795 + 5666673 * 2 ^ 59
def prefixEnd_5666673 : Nat := 4983230072969 + 3 ^ 40 * 5666673 * 2
def baseEnd_5666673 : Nat := 2909726960855412849526951

theorem tailTrace_5666673 : CollatzResearch.WordTrace tailWord_5666673 prefixEnd_5666673 2909726960855412849526951 := by
  unfold tailWord_5666673
  simp only [CollatzResearch.WordTrace]
  refine ⟨206680543799618986543756673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137787029199745991029171115 206680543799618986543756673)
  ·
    refine ⟨155010407849714239907817505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206680543799618986543756673 155010407849714239907817505)
    ·
      refine ⟨116257805887285679930863129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155010407849714239907817505 116257805887285679930863129)
      ·
        refine ⟨87193354415464259948147347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116257805887285679930863129 87193354415464259948147347)
        ·
          refine ⟨130790031623196389922221021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87193354415464259948147347 130790031623196389922221021)
          ·
            refine ⟨49046261858698646220832883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130790031623196389922221021 49046261858698646220832883)
            ·
              refine ⟨73569392788047969331249325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49046261858698646220832883 73569392788047969331249325)
              ·
                refine ⟨27588522295517988499218497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73569392788047969331249325 27588522295517988499218497)
                ·
                  refine ⟨20691391721638491374413873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27588522295517988499218497 20691391721638491374413873)
                  ·
                    refine ⟨15518543791228868530810405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20691391721638491374413873 15518543791228868530810405)
                    ·
                      refine ⟨2909726960855412849526951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15518543791228868530810405 2909726960855412849526951)
                      ·
                        rfl

theorem cell23_5666673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_5666673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666673 prefixEnd_5666673 := by exact prefixLift 5666673
  have htrace : WordTrace (prefixWord ++ tailWord_5666673) baseStart_5666673 baseEnd_5666673 := by
    simpa [prefixWord, tailWord_5666673, baseEnd_5666673] using wordTrace_append hprefix tailTrace_5666673
  have hstable : (prefixWord ++ tailWord_5666673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666673).length < 2 ^ (prefixWord ++ tailWord_5666673).sum := by decide
  have hdescent : baseEnd_5666673 < baseStart_5666673 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666713 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 4, 5]
def baseStart_5666713 : Nat := 118140960795 + 5666713 * 2 ^ 59
def prefixEnd_5666713 : Nat := 4983230072969 + 3 ^ 40 * 5666713 * 2
def baseEnd_5666713 : Nat := 969915833360530897675589

theorem tailTrace_5666713 : CollatzResearch.WordTrace tailWord_5666713 prefixEnd_5666713 969915833360530897675589 := by
  unfold tailWord_5666713
  simp only [CollatzResearch.WordTrace]
  refine ⟨206682002719474073375212793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137788001812982715583475195 206682002719474073375212793)
  ·
    refine ⟨155011502039605555031409595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206682002719474073375212793 155011502039605555031409595)
    ·
      refine ⟨232517253059408332547114393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155011502039605555031409595 232517253059408332547114393)
      ·
        refine ⟨174387939794556249410335795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232517253059408332547114393 174387939794556249410335795)
        ·
          refine ⟨261581909691834374115503693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174387939794556249410335795 261581909691834374115503693)
          ·
            refine ⟨98093216134437890293313885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261581909691834374115503693 98093216134437890293313885)
            ·
              refine ⟨36784956050414208859992707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98093216134437890293313885 36784956050414208859992707)
              ·
                refine ⟨55177434075621313289989061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36784956050414208859992707 55177434075621313289989061)
                ·
                  refine ⟨10345768889178996241872949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55177434075621313289989061 10345768889178996241872949)
                  ·
                    refine ⟨969915833360530897675589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10345768889178996241872949 969915833360530897675589)
                    ·
                      rfl

theorem cell23_5666713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 5].length) (baseStart_5666713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666713 prefixEnd_5666713 := by exact prefixLift 5666713
  have htrace : WordTrace (prefixWord ++ tailWord_5666713) baseStart_5666713 baseEnd_5666713 := by
    simpa [prefixWord, tailWord_5666713, baseEnd_5666713] using wordTrace_append hprefix tailTrace_5666713
  have hstable : (prefixWord ++ tailWord_5666713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666713).length < 2 ^ (prefixWord ++ tailWord_5666713).sum := by decide
  have hdescent : baseEnd_5666713 < baseStart_5666713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666720 : List Nat := [2, 1, 1, 4, 1, 1, 1, 3, 2, 5, 2]
def baseStart_5666720 : Nat := 118140960795 + 5666720 * 2 ^ 59
def prefixEnd_5666720 : Nat := 4983230072969 + 3 ^ 40 * 5666720 * 2
def baseEnd_5666720 : Nat := 2909751094446174165639235

theorem tailTrace_5666720 : CollatzResearch.WordTrace tailWord_5666720 prefixEnd_5666720 2909751094446174165639235 := by
  unfold tailWord_5666720
  simp only [CollatzResearch.WordTrace]
  refine ⟨103341129015224356785358807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137788172020299142380478409 103341129015224356785358807)
  ·
    refine ⟨155011693522836535178038211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103341129015224356785358807 155011693522836535178038211)
    ·
      refine ⟨232517540284254802767057317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155011693522836535178038211 232517540284254802767057317)
      ·
        refine ⟨43597038803297775518823247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232517540284254802767057317 43597038803297775518823247)
        ·
          refine ⟨65395558204946663278234871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43597038803297775518823247 65395558204946663278234871)
          ·
            refine ⟨98093337307419994917352307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65395558204946663278234871 98093337307419994917352307)
            ·
              refine ⟨147140005961129992376028461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98093337307419994917352307 147140005961129992376028461)
              ·
                refine ⟨55177502235423747141010673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147140005961129992376028461 55177502235423747141010673)
                ·
                  refine ⟨41383126676567810355758005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55177502235423747141010673 41383126676567810355758005)
                  ·
                    refine ⟨3879668125928232220852313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41383126676567810355758005 3879668125928232220852313)
                    ·
                      refine ⟨2909751094446174165639235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3879668125928232220852313 2909751094446174165639235)
                      ·
                        rfl

theorem cell23_5666720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 2, 5, 2].length) (baseStart_5666720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666720 prefixEnd_5666720 := by exact prefixLift 5666720
  have htrace : WordTrace (prefixWord ++ tailWord_5666720) baseStart_5666720 baseEnd_5666720 := by
    simpa [prefixWord, tailWord_5666720, baseEnd_5666720] using wordTrace_append hprefix tailTrace_5666720
  have hstable : (prefixWord ++ tailWord_5666720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666720).length < 2 ^ (prefixWord ++ tailWord_5666720).sum := by decide
  have hdescent : baseEnd_5666720 < baseStart_5666720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666728 : List Nat := [2, 1, 6, 2, 1, 1, 1, 3, 2, 2, 2]
def baseStart_5666728 : Nat := 118140960795 + 5666728 * 2 ^ 59
def prefixEnd_5666728 : Nat := 4983230072969 + 3 ^ 40 * 5666728 * 2
def baseEnd_5666728 : Nat := 2909755202291410134339199

theorem tailTrace_5666728 : CollatzResearch.WordTrace tailWord_5666728 prefixEnd_5666728 2909755202291410134339199 := by
  unfold tailWord_5666728
  simp only [CollatzResearch.WordTrace]
  refine ⟨103341274907209865468504419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137788366542946487291339225 103341274907209865468504419)
  ·
    refine ⟨155011912360814798202756629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103341274907209865468504419 155011912360814798202756629)
    ·
      refine ⟨7266183391913193665754217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 155011912360814798202756629 7266183391913193665754217)
      ·
        refine ⟨5449637543934895249315663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7266183391913193665754217 5449637543934895249315663)
        ·
          refine ⟨8174456315902342873973495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5449637543934895249315663 8174456315902342873973495)
          ·
            refine ⟨12261684473853514310960243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8174456315902342873973495 12261684473853514310960243)
            ·
              refine ⟨18392526710780271466440365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12261684473853514310960243 18392526710780271466440365)
              ·
                refine ⟨6897197516542601799915137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18392526710780271466440365 6897197516542601799915137)
                ·
                  refine ⟨5172898137406951349936353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6897197516542601799915137 5172898137406951349936353)
                  ·
                    refine ⟨3879673603055213512452265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5172898137406951349936353 3879673603055213512452265)
                    ·
                      refine ⟨2909755202291410134339199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3879673603055213512452265 2909755202291410134339199)
                      ·
                        rfl

theorem cell23_5666728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_5666728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666728 prefixEnd_5666728 := by exact prefixLift 5666728
  have htrace : WordTrace (prefixWord ++ tailWord_5666728) baseStart_5666728 baseEnd_5666728 := by
    simpa [prefixWord, tailWord_5666728, baseEnd_5666728] using wordTrace_append hprefix tailTrace_5666728
  have hstable : (prefixWord ++ tailWord_5666728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666728).length < 2 ^ (prefixWord ++ tailWord_5666728).sum := by decide
  have hdescent : baseEnd_5666728 < baseStart_5666728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666763 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 6]
def baseStart_5666763 : Nat := 118140960795 + 5666763 * 2 ^ 59
def prefixEnd_5666763 : Nat := 4983230072969 + 3 ^ 40 * 5666763 * 2
def baseEnd_5666763 : Nat := 2909773174114317497401537

theorem tailTrace_5666763 : CollatzResearch.WordTrace tailWord_5666763 prefixEnd_5666763 2909773174114317497401537 := by
  unfold tailWord_5666763
  simp only [CollatzResearch.WordTrace]
  refine ⟨206683826369292931914532943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137789217579528621276355295 206683826369292931914532943)
  ·
    refine ⟨310025739553939397871799415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206683826369292931914532943 310025739553939397871799415)
    ·
      refine ⟨465038609330909096807699123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310025739553939397871799415 465038609330909096807699123)
      ·
        refine ⟨697557913996363645211548685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465038609330909096807699123 697557913996363645211548685)
        ·
          refine ⟨261584217748636366954330757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 697557913996363645211548685 261584217748636366954330757)
          ·
            refine ⟨49047040827869318803937017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 261584217748636366954330757 49047040827869318803937017)
            ·
              refine ⟨36785280620901989102952763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49047040827869318803937017 36785280620901989102952763)
              ·
                refine ⟨55177920931352983654429145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36785280620901989102952763 55177920931352983654429145)
                ·
                  refine ⟨41383440698514737740821859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55177920931352983654429145 41383440698514737740821859)
                  ·
                    refine ⟨62075161047772106611232789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41383440698514737740821859 62075161047772106611232789)
                    ·
                      refine ⟨2909773174114317497401537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62075161047772106611232789 2909773174114317497401537)
                      ·
                        rfl

theorem cell23_5666763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 6].length) (baseStart_5666763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666763 prefixEnd_5666763 := by exact prefixLift 5666763
  have htrace : WordTrace (prefixWord ++ tailWord_5666763) baseStart_5666763 baseEnd_5666763 := by
    simpa [prefixWord, tailWord_5666763, baseEnd_5666763] using wordTrace_append hprefix tailTrace_5666763
  have hstable : (prefixWord ++ tailWord_5666763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666763).length < 2 ^ (prefixWord ++ tailWord_5666763).sum := by decide
  have hdescent : baseEnd_5666763 < baseStart_5666763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666817 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_5666817 : Nat := 118140960795 + 5666817 * 2 ^ 59
def prefixEnd_5666817 : Nat := 4983230072969 + 3 ^ 40 * 5666817 * 2
def baseEnd_5666817 : Nat := 2909800902069660286126289

theorem tailTrace_5666817 : CollatzResearch.WordTrace tailWord_5666817 prefixEnd_5666817 2909800902069660286126289 := by
  unfold tailWord_5666817
  simp only [CollatzResearch.WordTrace]
  refine ⟨206685795911097299136998705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137790530607398199424665803 206685795911097299136998705)
  ·
    refine ⟨155014346933322974352749029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206685795911097299136998705 155014346933322974352749029)
    ·
      refine ⟨29065190049998057691140443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155014346933322974352749029 29065190049998057691140443)
      ·
        refine ⟨43597785074997086536710665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29065190049998057691140443 43597785074997086536710665)
        ·
          refine ⟨32698338806247814902532999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43597785074997086536710665 32698338806247814902532999)
          ·
            refine ⟨49047508209371722353799499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32698338806247814902532999 49047508209371722353799499)
            ·
              refine ⟨73571262314057583530699249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49047508209371722353799499 73571262314057583530699249)
              ·
                refine ⟨55178446735543187648024437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73571262314057583530699249 55178446735543187648024437)
                ·
                  refine ⟨5172979381457173842002291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55178446735543187648024437 5172979381457173842002291)
                  ·
                    refine ⟨7759469072185760763003437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5172979381457173842002291 7759469072185760763003437)
                    ·
                      refine ⟨2909800902069660286126289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7759469072185760763003437 2909800902069660286126289)
                      ·
                        rfl

theorem cell23_5666817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_5666817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666817 prefixEnd_5666817 := by exact prefixLift 5666817
  have htrace : WordTrace (prefixWord ++ tailWord_5666817) baseStart_5666817 baseEnd_5666817 := by
    simpa [prefixWord, tailWord_5666817, baseEnd_5666817] using wordTrace_append hprefix tailTrace_5666817
  have hstable : (prefixWord ++ tailWord_5666817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666817).length < 2 ^ (prefixWord ++ tailWord_5666817).sum := by decide
  have hdescent : baseEnd_5666817 < baseStart_5666817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666827 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 4, 3, 2]
def baseStart_5666827 : Nat := 118140960795 + 5666827 * 2 ^ 59
def prefixEnd_5666827 : Nat := 4983230072969 + 3 ^ 40 * 5666827 * 2
def baseEnd_5666827 : Nat := 2909806036876205247001243

theorem tailTrace_5666827 : CollatzResearch.WordTrace tailWord_5666827 prefixEnd_5666827 2909806036876205247001243 := by
  unfold tailWord_5666827
  simp only [CollatzResearch.WordTrace]
  refine ⟨206686160641061070844862735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137790773760707380563241823 206686160641061070844862735)
  ·
    refine ⟨310029240961591606267294103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206686160641061070844862735 310029240961591606267294103)
    ·
      refine ⟨465043861442387409400941155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310029240961591606267294103 465043861442387409400941155)
      ·
        refine ⟨697565792163581114101411733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465043861442387409400941155 697565792163581114101411733)
        ·
          refine ⟨32698396507667864723503675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 697565792163581114101411733 32698396507667864723503675)
          ·
            refine ⟨49047594761501797085255513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32698396507667864723503675 49047594761501797085255513)
            ·
              refine ⟨36785696071126347813941635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49047594761501797085255513 36785696071126347813941635)
              ·
                refine ⟨55178544106689521720912453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36785696071126347813941635 55178544106689521720912453)
                ·
                  refine ⟨10345977020004285322671085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55178544106689521720912453 10345977020004285322671085)
                  ·
                    refine ⟨3879741382501606996001657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10345977020004285322671085 3879741382501606996001657)
                    ·
                      refine ⟨2909806036876205247001243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3879741382501606996001657 2909806036876205247001243)
                      ·
                        rfl

theorem cell23_5666827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 3, 2].length) (baseStart_5666827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666827 prefixEnd_5666827 := by exact prefixLift 5666827
  have htrace : WordTrace (prefixWord ++ tailWord_5666827) baseStart_5666827 baseEnd_5666827 := by
    simpa [prefixWord, tailWord_5666827, baseEnd_5666827] using wordTrace_append hprefix tailTrace_5666827
  have hstable : (prefixWord ++ tailWord_5666827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666827).length < 2 ^ (prefixWord ++ tailWord_5666827).sum := by decide
  have hdescent : baseEnd_5666827 < baseStart_5666827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666833 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 2, 10]
def baseStart_5666833 : Nat := 118140960795 + 5666833 * 2 ^ 59
def prefixEnd_5666833 : Nat := 4983230072969 + 3 ^ 40 * 5666833 * 2
def baseEnd_5666833 : Nat := 969936372586710741175405

theorem tailTrace_5666833 : CollatzResearch.WordTrace tailWord_5666833 prefixEnd_5666833 969936372586710741175405 := by
  unfold tailWord_5666833
  simp only [CollatzResearch.WordTrace]
  refine ⟨206686379479039333869581153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137790919652692889246387435 206686379479039333869581153)
  ·
    refine ⟨155014784609279500402185865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206686379479039333869581153 155014784609279500402185865)
    ·
      refine ⟨116261088456959625301639399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155014784609279500402185865 116261088456959625301639399)
      ·
        refine ⟨174391632685439437952459099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116261088456959625301639399 174391632685439437952459099)
        ·
          refine ⟨261587449028159156928688649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174391632685439437952459099 261587449028159156928688649)
          ·
            refine ⟨196190586771119367696516487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261587449028159156928688649 196190586771119367696516487)
            ·
              refine ⟨294285880156679051544774731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196190586771119367696516487 294285880156679051544774731)
              ·
                refine ⟨441428820235018577317162097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294285880156679051544774731 441428820235018577317162097)
                ·
                  refine ⟨331071615176263932987871573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441428820235018577317162097 331071615176263932987871573)
                  ·
                    refine ⟨969936372586710741175405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 331071615176263932987871573 969936372586710741175405)
                    ·
                      rfl

theorem cell23_5666833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_5666833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666833 prefixEnd_5666833 := by exact prefixLift 5666833
  have htrace : WordTrace (prefixWord ++ tailWord_5666833) baseStart_5666833 baseEnd_5666833 := by
    simpa [prefixWord, tailWord_5666833, baseEnd_5666833] using wordTrace_append hprefix tailTrace_5666833
  have hstable : (prefixWord ++ tailWord_5666833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666833).length < 2 ^ (prefixWord ++ tailWord_5666833).sum := by decide
  have hdescent : baseEnd_5666833 < baseStart_5666833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666877 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 1, 1, 5]
def baseStart_5666877 : Nat := 118140960795 + 5666877 * 2 ^ 59
def prefixEnd_5666877 : Nat := 4983230072969 + 3 ^ 40 * 5666877 * 2
def baseEnd_5666877 : Nat := 2909831710908930051376013

theorem tailTrace_5666877 : CollatzResearch.WordTrace tailWord_5666877 prefixEnd_5666877 2909831710908930051376013 := by
  unfold tailWord_5666877
  simp only [CollatzResearch.WordTrace]
  refine ⟨206687984290879929384182885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137791989527253286256121923 206687984290879929384182885)
  ·
    refine ⟨38753997054539986759534291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206687984290879929384182885 38753997054539986759534291)
    ·
      refine ⟨58130995581809980139301437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38753997054539986759534291 58130995581809980139301437)
      ·
        refine ⟨21799123343178742552238039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58130995581809980139301437 21799123343178742552238039)
        ·
          refine ⟨32698685014768113828357059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21799123343178742552238039 32698685014768113828357059)
          ·
            refine ⟨49048027522152170742535589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32698685014768113828357059 49048027522152170742535589)
            ·
              refine ⟨9196505160403532014225423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49048027522152170742535589 9196505160403532014225423)
              ·
                refine ⟨13794757740605298021338135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9196505160403532014225423 13794757740605298021338135)
                ·
                  refine ⟨20692136610907947032007203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13794757740605298021338135 20692136610907947032007203)
                  ·
                    refine ⟨31038204916361920548010805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20692136610907947032007203 31038204916361920548010805)
                    ·
                      refine ⟨2909831710908930051376013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31038204916361920548010805 2909831710908930051376013)
                      ·
                        rfl

theorem cell23_5666877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_5666877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666877 prefixEnd_5666877 := by exact prefixLift 5666877
  have htrace : WordTrace (prefixWord ++ tailWord_5666877) baseStart_5666877 baseEnd_5666877 := by
    simpa [prefixWord, tailWord_5666877, baseEnd_5666877] using wordTrace_append hprefix tailTrace_5666877
  have hstable : (prefixWord ++ tailWord_5666877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666877).length < 2 ^ (prefixWord ++ tailWord_5666877).sum := by decide
  have hdescent : baseEnd_5666877 < baseStart_5666877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666880 : List Nat := [2, 1, 1, 2, 2, 6, 9]
def baseStart_5666880 : Nat := 118140960795 + 5666880 * 2 ^ 59
def prefixEnd_5666880 : Nat := 4983230072969 + 3 ^ 40 * 5666880 * 2
def baseEnd_5666880 : Nat := 35923867300628315304179

theorem tailTrace_5666880 : CollatzResearch.WordTrace tailWord_5666880 prefixEnd_5666880 35923867300628315304179 := by
  unfold tailWord_5666880
  simp only [CollatzResearch.WordTrace]
  refine ⟨103344046854934530448271047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137792062473246040597694729 103344046854934530448271047)
  ·
    refine ⟨155016070282401795672406571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103344046854934530448271047 155016070282401795672406571)
    ·
      refine ⟨232524105423602693508609857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155016070282401795672406571 232524105423602693508609857)
      ·
        refine ⟨174393079067702020131457393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232524105423602693508609857 174393079067702020131457393)
        ·
          refine ⟨130794809300776515098593045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174393079067702020131457393 130794809300776515098593045)
          ·
            refine ⟨6131006685973899145246549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 130794809300776515098593045 6131006685973899145246549)
            ·
              refine ⟨35923867300628315304179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6131006685973899145246549 35923867300628315304179)
              ·
                rfl

theorem cell23_5666880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 9].length) (baseStart_5666880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666880 prefixEnd_5666880 := by exact prefixLift 5666880
  have htrace : WordTrace (prefixWord ++ tailWord_5666880) baseStart_5666880 baseEnd_5666880 := by
    simpa [prefixWord, tailWord_5666880, baseEnd_5666880] using wordTrace_append hprefix tailTrace_5666880
  have hstable : (prefixWord ++ tailWord_5666880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666880).length < 2 ^ (prefixWord ++ tailWord_5666880).sum := by decide
  have hdescent : baseEnd_5666880 < baseStart_5666880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666900 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_5666900 : Nat := 118140960795 + 5666900 * 2 ^ 59
def prefixEnd_5666900 : Nat := 4983230072969 + 3 ^ 40 * 5666900 * 2
def baseEnd_5666900 : Nat := 2909843520963983461388407

theorem tailTrace_5666900 : CollatzResearch.WordTrace tailWord_5666900 prefixEnd_5666900 2909843520963983461388407 := by
  unfold tailWord_5666900
  simp only [CollatzResearch.WordTrace]
  refine ⟨103344411584898302156135077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137792548779864402874846769 103344411584898302156135077)
  ·
    refine ⟨19377077172168431654275327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103344411584898302156135077 19377077172168431654275327)
    ·
      refine ⟨29065615758252647481412991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19377077172168431654275327 29065615758252647481412991)
      ·
        refine ⟨43598423637378971222119487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29065615758252647481412991 43598423637378971222119487)
        ·
          refine ⟨65397635456068456833179231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43598423637378971222119487 65397635456068456833179231)
          ·
            refine ⟨98096453184102685249768847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65397635456068456833179231 98096453184102685249768847)
            ·
              refine ⟨147144679776154027874653271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98096453184102685249768847 147144679776154027874653271)
              ·
                refine ⟨220717019664231041811979907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147144679776154027874653271 220717019664231041811979907)
                ·
                  refine ⟨331075529496346562717969861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220717019664231041811979907 331075529496346562717969861)
                  ·
                    refine ⟨62076661780564980509619349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 331075529496346562717969861 62076661780564980509619349)
                    ·
                      refine ⟨2909843520963983461388407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62076661780564980509619349 2909843520963983461388407)
                      ·
                        rfl

theorem cell23_5666900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_5666900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666900 prefixEnd_5666900 := by exact prefixLift 5666900
  have htrace : WordTrace (prefixWord ++ tailWord_5666900) baseStart_5666900 baseEnd_5666900 := by
    simpa [prefixWord, tailWord_5666900, baseEnd_5666900] using wordTrace_append hprefix tailTrace_5666900
  have hstable : (prefixWord ++ tailWord_5666900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666900).length < 2 ^ (prefixWord ++ tailWord_5666900).sum := by decide
  have hdescent : baseEnd_5666900 < baseStart_5666900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666901 : List Nat := [1, 3, 2, 2, 1, 5, 2, 1, 2, 4]
def baseStart_5666901 : Nat := 118140960795 + 5666901 * 2 ^ 59
def prefixEnd_5666901 : Nat := 4983230072969 + 3 ^ 40 * 5666901 * 2
def baseEnd_5666901 : Nat := 969948011481545985825301

theorem tailTrace_5666901 : CollatzResearch.WordTrace tailWord_5666901 prefixEnd_5666901 969948011481545985825301 := by
  unfold tailWord_5666901
  simp only [CollatzResearch.WordTrace]
  refine ⟨206688859642792981483056557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137792573095195320988704371 206688859642792981483056557)
  ·
    refine ⟨77508322366047368056146209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206688859642792981483056557 77508322366047368056146209)
    ·
      refine ⟨58131241774535526042109657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77508322366047368056146209 58131241774535526042109657)
      ·
        refine ⟨43598431330901644531582243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58131241774535526042109657 43598431330901644531582243)
        ·
          refine ⟨65397646996352466797373365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43598431330901644531582243 65397646996352466797373365)
          ·
            refine ⟨6131029405908043762253753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65397646996352466797373365 6131029405908043762253753)
            ·
              refine ⟨4598272054431032821690315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6131029405908043762253753 4598272054431032821690315)
              ·
                refine ⟨6897408081646549232535473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4598272054431032821690315 6897408081646549232535473)
                ·
                  refine ⟨5173056061234911924401605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6897408081646549232535473 5173056061234911924401605)
                  ·
                    refine ⟨969948011481545985825301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5173056061234911924401605 969948011481545985825301)
                    ·
                      rfl

theorem cell23_5666901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_5666901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666901 prefixEnd_5666901 := by exact prefixLift 5666901
  have htrace : WordTrace (prefixWord ++ tailWord_5666901) baseStart_5666901 baseEnd_5666901 := by
    simpa [prefixWord, tailWord_5666901, baseEnd_5666901] using wordTrace_append hprefix tailTrace_5666901
  have hstable : (prefixWord ++ tailWord_5666901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666901).length < 2 ^ (prefixWord ++ tailWord_5666901).sum := by decide
  have hdescent : baseEnd_5666901 < baseStart_5666901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5666941 : List Nat := [1, 4, 1, 1, 3, 3, 2, 2, 2, 1, 3]
def baseStart_5666941 : Nat := 118140960795 + 5666941 * 2 ^ 59
def prefixEnd_5666941 : Nat := 4983230072969 + 3 ^ 40 * 5666941 * 2
def baseEnd_5666941 : Nat := 2909864573670817800975719

theorem tailTrace_5666941 : CollatzResearch.WordTrace tailWord_5666941 prefixEnd_5666941 2909864573670817800975719 := by
  unfold tailWord_5666941
  simp only [CollatzResearch.WordTrace]
  refine ⟨206690318562648068314512677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137793545708432045543008451 206690318562648068314512677)
  ·
    refine ⟨38754434730496512808971127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206690318562648068314512677 38754434730496512808971127)
    ·
      refine ⟨58131652095744769213456691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38754434730496512808971127 58131652095744769213456691)
      ·
        refine ⟨87197478143617153820185037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58131652095744769213456691 87197478143617153820185037)
        ·
          refine ⟨32699054303856432682569389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87197478143617153820185037 32699054303856432682569389)
          ·
            refine ⟨12262145363946162255963521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32699054303856432682569389 12262145363946162255963521)
            ·
              refine ⟨9196609022959621691972641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12262145363946162255963521 9196609022959621691972641)
              ·
                refine ⟨6897456767219716268979481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9196609022959621691972641 6897456767219716268979481)
                ·
                  refine ⟨5173092575414787201734611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6897456767219716268979481 5173092575414787201734611)
                  ·
                    refine ⟨7759638863122180802601917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5173092575414787201734611 7759638863122180802601917)
                    ·
                      refine ⟨2909864573670817800975719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7759638863122180802601917 2909864573670817800975719)
                      ·
                        rfl

theorem cell23_5666941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_5666941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5666941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5666941 prefixEnd_5666941 := by exact prefixLift 5666941
  have htrace : WordTrace (prefixWord ++ tailWord_5666941) baseStart_5666941 baseEnd_5666941 := by
    simpa [prefixWord, tailWord_5666941, baseEnd_5666941] using wordTrace_append hprefix tailTrace_5666941
  have hstable : (prefixWord ++ tailWord_5666941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5666941).length < 2 ^ (prefixWord ++ tailWord_5666941).sum := by decide
  have hdescent : baseEnd_5666941 < baseStart_5666941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5666941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667004 : List Nat := [2, 2, 2, 3, 3, 1, 2, 1, 7]
def baseStart_5667004 : Nat := 118140960795 + 5667004 * 2 ^ 59
def prefixEnd_5667004 : Nat := 4983230072969 + 3 ^ 40 * 5667004 * 2
def baseEnd_5667004 : Nat := 323321880328005672720881

theorem tailTrace_5667004 : CollatzResearch.WordTrace tailWord_5667004 prefixEnd_5667004 323321880328005672720881 := by
  unfold tailWord_5667004
  simp only [CollatzResearch.WordTrace]
  refine ⟨103346308180709915037028033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137795077574279886716037377 103346308180709915037028033)
  ·
    refine ⟨77509731135532436277771025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103346308180709915037028033 77509731135532436277771025)
    ·
      refine ⟨58132298351649327208328269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77509731135532436277771025 58132298351649327208328269)
      ·
        refine ⟨21799611881868497703123101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58132298351649327208328269 21799611881868497703123101)
        ·
          refine ⟨8174854455700686638671163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21799611881868497703123101 8174854455700686638671163)
          ·
            refine ⟨12262281683551029958006745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8174854455700686638671163 12262281683551029958006745)
            ·
              refine ⟨9196711262663272468505059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12262281683551029958006745 9196711262663272468505059)
              ·
                refine ⟨13795066893994908702757589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9196711262663272468505059 13795066893994908702757589)
                ·
                  refine ⟨323321880328005672720881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13795066893994908702757589 323321880328005672720881)
                  ·
                    rfl

theorem cell23_5667004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 1, 7].length) (baseStart_5667004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667004 prefixEnd_5667004 := by exact prefixLift 5667004
  have htrace : WordTrace (prefixWord ++ tailWord_5667004) baseStart_5667004 baseEnd_5667004 := by
    simpa [prefixWord, tailWord_5667004, baseEnd_5667004] using wordTrace_append hprefix tailTrace_5667004
  have hstable : (prefixWord ++ tailWord_5667004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667004).length < 2 ^ (prefixWord ++ tailWord_5667004).sum := by decide
  have hdescent : baseEnd_5667004 < baseStart_5667004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667087 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 3]
def baseStart_5667087 : Nat := 118140960795 + 5667087 * 2 ^ 59
def prefixEnd_5667087 : Nat := 4983230072969 + 3 ^ 40 * 5667087 * 2
def baseEnd_5667087 : Nat := 2909939541846374229750047

theorem tailTrace_5667087 : CollatzResearch.WordTrace tailWord_5667087 prefixEnd_5667087 2909939541846374229750047 := by
  unfold tailWord_5667087
  simp only [CollatzResearch.WordTrace]
  refine ⟨206695643620119135249327515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137797095746746090166218343 206695643620119135249327515)
  ·
    refine ⟨310043465430178702873991273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206695643620119135249327515 310043465430178702873991273)
    ·
      refine ⟨232532599072634027155493455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310043465430178702873991273 232532599072634027155493455)
      ·
        refine ⟨348798898608951040733240183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232532599072634027155493455 348798898608951040733240183)
        ·
          refine ⟨523198347913426561099860275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348798898608951040733240183 523198347913426561099860275)
          ·
            refine ⟨784797521870139841649790413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523198347913426561099860275 784797521870139841649790413)
            ·
              refine ⟨294299070701302440618671405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 784797521870139841649790413 294299070701302440618671405)
              ·
                refine ⟨110362151512988415232001777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294299070701302440618671405 110362151512988415232001777)
                ·
                  refine ⟨82771613634741311424001333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110362151512988415232001777 82771613634741311424001333)
                  ·
                    refine ⟨7759838778256997946000125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82771613634741311424001333 7759838778256997946000125)
                    ·
                      refine ⟨2909939541846374229750047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7759838778256997946000125 2909939541846374229750047)
                      ·
                        rfl

theorem cell23_5667087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 3].length) (baseStart_5667087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667087 prefixEnd_5667087 := by exact prefixLift 5667087
  have htrace : WordTrace (prefixWord ++ tailWord_5667087) baseStart_5667087 baseEnd_5667087 := by
    simpa [prefixWord, tailWord_5667087, baseEnd_5667087] using wordTrace_append hprefix tailTrace_5667087
  have hstable : (prefixWord ++ tailWord_5667087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667087).length < 2 ^ (prefixWord ++ tailWord_5667087).sum := by decide
  have hdescent : baseEnd_5667087 < baseStart_5667087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667144 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 3, 1, 4]
def baseStart_5667144 : Nat := 118140960795 + 5667144 * 2 ^ 59
def prefixEnd_5667144 : Nat := 4983230072969 + 3 ^ 40 * 5667144 * 2
def baseEnd_5667144 : Nat := 2909968810243680506737285

theorem tailTrace_5667144 : CollatzResearch.WordTrace tailWord_5667144 prefixEnd_5667144 2909968810243680506737285 := by
  unfold tailWord_5667144
  simp only [CollatzResearch.WordTrace]
  refine ⟨103348861290456316992076243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137798481720608422656101657 103348861290456316992076243)
  ·
    refine ⟨155023291935684475488114365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103348861290456316992076243 155023291935684475488114365)
    ·
      refine ⟨58133734475881678308042887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155023291935684475488114365 58133734475881678308042887)
      ·
        refine ⟨87200601713822517462064331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58133734475881678308042887 87200601713822517462064331)
        ·
          refine ⟨130800902570733776193096497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87200601713822517462064331 130800902570733776193096497)
          ·
            refine ⟨98100676928050332144822373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130800902570733776193096497 98100676928050332144822373)
            ·
              refine ⟨18393876924009437277154195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98100676928050332144822373 18393876924009437277154195)
              ·
                refine ⟨27590815386014155915731293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18393876924009437277154195 27590815386014155915731293)
                ·
                  refine ⟨10346555769755308468399235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27590815386014155915731293 10346555769755308468399235)
                  ·
                    refine ⟨15519833654632962702598853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10346555769755308468399235 15519833654632962702598853)
                    ·
                      refine ⟨2909968810243680506737285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15519833654632962702598853 2909968810243680506737285)
                      ·
                        rfl

theorem cell23_5667144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_5667144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667144 prefixEnd_5667144 := by exact prefixLift 5667144
  have htrace : WordTrace (prefixWord ++ tailWord_5667144) baseStart_5667144 baseEnd_5667144 := by
    simpa [prefixWord, tailWord_5667144, baseEnd_5667144] using wordTrace_append hprefix tailTrace_5667144
  have hstable : (prefixWord ++ tailWord_5667144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667144).length < 2 ^ (prefixWord ++ tailWord_5667144).sum := by decide
  have hdescent : baseEnd_5667144 < baseStart_5667144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667147 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 5]
def baseStart_5667147 : Nat := 118140960795 + 5667147 * 2 ^ 59
def prefixEnd_5667147 : Nat := 4983230072969 + 3 ^ 40 * 5667147 * 2
def baseEnd_5667147 : Nat := 2909970350685643994999771

theorem tailTrace_5667147 : CollatzResearch.WordTrace tailWord_5667147 prefixEnd_5667147 2909970350685643994999771 := by
  unfold tailWord_5667147
  simp only [CollatzResearch.WordTrace]
  refine ⟨206697831999901765496511695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137798554666601176997674463 206697831999901765496511695)
  ·
    refine ⟨310046747999852648244767543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206697831999901765496511695 310046747999852648244767543)
    ·
      refine ⟨465070121999778972367151315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310046747999852648244767543 465070121999778972367151315)
      ·
        refine ⟨697605182999668458550726973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465070121999778972367151315 697605182999668458550726973)
        ·
          refine ⟨261601943624875671956522615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 697605182999668458550726973 261601943624875671956522615)
          ·
            refine ⟨392402915437313507934783923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261601943624875671956522615 392402915437313507934783923)
            ·
              refine ⟨588604373155970261902175885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392402915437313507934783923 588604373155970261902175885)
              ·
                refine ⟨220726639933488848213315957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 588604373155970261902175885 220726639933488848213315957)
                ·
                  refine ⟨20693122493764579519998371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 220726639933488848213315957 20693122493764579519998371)
                  ·
                    refine ⟨31039683740646869279997557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20693122493764579519998371 31039683740646869279997557)
                    ·
                      refine ⟨2909970350685643994999771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31039683740646869279997557 2909970350685643994999771)
                      ·
                        rfl

theorem cell23_5667147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 5].length) (baseStart_5667147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667147 prefixEnd_5667147 := by exact prefixLift 5667147
  have htrace : WordTrace (prefixWord ++ tailWord_5667147) baseStart_5667147 baseEnd_5667147 := by
    simpa [prefixWord, tailWord_5667147, baseEnd_5667147] using wordTrace_append hprefix tailTrace_5667147
  have hstable : (prefixWord ++ tailWord_5667147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667147).length < 2 ^ (prefixWord ++ tailWord_5667147).sum := by decide
  have hdescent : baseEnd_5667147 < baseStart_5667147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667154 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 1, 6]
def baseStart_5667154 : Nat := 118140960795 + 5667154 * 2 ^ 59
def prefixEnd_5667154 : Nat := 4983230072969 + 3 ^ 40 * 5667154 * 2
def baseEnd_5667154 : Nat := 969991315016741822537413

theorem tailTrace_5667154 : CollatzResearch.WordTrace tailWord_5667154 prefixEnd_5667154 969991315016741822537413 := by
  unfold tailWord_5667154
  simp only [CollatzResearch.WordTrace]
  refine ⟨51674521827719101423004129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137798724873917603794677677 51674521827719101423004129)
  ·
    refine ⟨38755891370789326067253097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51674521827719101423004129 38755891370789326067253097)
    ·
      refine ⟨29066918528091994550439823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38755891370789326067253097 29066918528091994550439823)
      ·
        refine ⟨43600377792137991825659735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29066918528091994550439823 43600377792137991825659735)
        ·
          refine ⟨65400566688206987738489603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43600377792137991825659735 65400566688206987738489603)
          ·
            refine ⟨98100850032310481607734405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65400566688206987738489603 98100850032310481607734405)
            ·
              refine ⟨18393909381058215301450201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98100850032310481607734405 18393909381058215301450201)
              ·
                refine ⟨13795432035793661476087651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18393909381058215301450201 13795432035793661476087651)
                ·
                  refine ⟨20693148053690492214131477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13795432035793661476087651 20693148053690492214131477)
                  ·
                    refine ⟨969991315016741822537413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20693148053690492214131477 969991315016741822537413)
                    ·
                      rfl

theorem cell23_5667154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_5667154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667154 prefixEnd_5667154 := by exact prefixLift 5667154
  have htrace : WordTrace (prefixWord ++ tailWord_5667154) baseStart_5667154 baseEnd_5667154 := by
    simpa [prefixWord, tailWord_5667154, baseEnd_5667154] using wordTrace_append hprefix tailTrace_5667154
  have hstable : (prefixWord ++ tailWord_5667154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667154).length < 2 ^ (prefixWord ++ tailWord_5667154).sum := by decide
  have hdescent : baseEnd_5667154 < baseStart_5667154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667161 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 7, 2, 2]
def baseStart_5667161 : Nat := 118140960795 + 5667161 * 2 ^ 59
def prefixEnd_5667161 : Nat := 4983230072969 + 3 ^ 40 * 5667161 * 2
def baseEnd_5667161 : Nat := 2909977539414806940224707

theorem tailTrace_5667161 : CollatzResearch.WordTrace tailWord_5667161 prefixEnd_5667161 2909977539414806940224707 := by
  unfold tailWord_5667161
  simp only [CollatzResearch.WordTrace]
  refine ⟨206698342621851045887521337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137798895081234030591680891 206698342621851045887521337)
  ·
    refine ⟨155023756966388284415641003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206698342621851045887521337 155023756966388284415641003)
    ·
      refine ⟨232535635449582426623461505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155023756966388284415641003 232535635449582426623461505)
      ·
        refine ⟨174401726587186819967596129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232535635449582426623461505 174401726587186819967596129)
        ·
          refine ⟨130801294940390114975697097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174401726587186819967596129 130801294940390114975697097)
          ·
            refine ⟨98100971205292586231772823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130801294940390114975697097 98100971205292586231772823)
            ·
              refine ⟨147151456807938879347659235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98100971205292586231772823 147151456807938879347659235)
              ·
                refine ⟨220727185211908319021488853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147151456807938879347659235 220727185211908319021488853)
                ·
                  refine ⟨5173293403404101227066145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 220727185211908319021488853 5173293403404101227066145)
                  ·
                    refine ⟨3879970052553075920299609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5173293403404101227066145 3879970052553075920299609)
                    ·
                      refine ⟨2909977539414806940224707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3879970052553075920299609 2909977539414806940224707)
                      ·
                        rfl

theorem cell23_5667161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 7, 2, 2].length) (baseStart_5667161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667161 prefixEnd_5667161 := by exact prefixLift 5667161
  have htrace : WordTrace (prefixWord ++ tailWord_5667161) baseStart_5667161 baseEnd_5667161 := by
    simpa [prefixWord, tailWord_5667161, baseEnd_5667161] using wordTrace_append hprefix tailTrace_5667161
  have hstable : (prefixWord ++ tailWord_5667161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667161).length < 2 ^ (prefixWord ++ tailWord_5667161).sum := by decide
  have hdescent : baseEnd_5667161 < baseStart_5667161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667187 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 6]
def baseStart_5667187 : Nat := 118140960795 + 5667187 * 2 ^ 59
def prefixEnd_5667187 : Nat := 4983230072969 + 3 ^ 40 * 5667187 * 2
def baseEnd_5667187 : Nat := 2909990889911823838499587

theorem tailTrace_5667187 : CollatzResearch.WordTrace tailWord_5667187 prefixEnd_5667187 2909990889911823838499587 := by
  unfold tailWord_5667187
  simp only [CollatzResearch.WordTrace]
  refine ⟨206699290919756852327967815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137799527279837901551978543 206699290919756852327967815)
  ·
    refine ⟨310048936379635278491951723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206699290919756852327967815 310048936379635278491951723)
    ·
      refine ⟨465073404569452917737927585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310048936379635278491951723 465073404569452917737927585)
      ·
        refine ⟨348805053427089688303445689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465073404569452917737927585 348805053427089688303445689)
        ·
          refine ⟨261603790070317266227584267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348805053427089688303445689 261603790070317266227584267)
          ·
            refine ⟨392405685105475899341376401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261603790070317266227584267 392405685105475899341376401)
            ·
              refine ⟨294304263829106924506032301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 392405685105475899341376401 294304263829106924506032301)
              ·
                refine ⟨110364098935915096689762113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294304263829106924506032301 110364098935915096689762113)
                ·
                  refine ⟨82773074201936322517321585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110364098935915096689762113 82773074201936322517321585)
                  ·
                    refine ⟨62079805651452241887991189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82773074201936322517321585 62079805651452241887991189)
                    ·
                      refine ⟨2909990889911823838499587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62079805651452241887991189 2909990889911823838499587)
                      ·
                        rfl

theorem cell23_5667187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_5667187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667187 prefixEnd_5667187 := by exact prefixLift 5667187
  have htrace : WordTrace (prefixWord ++ tailWord_5667187) baseStart_5667187 baseEnd_5667187 := by
    simpa [prefixWord, tailWord_5667187, baseEnd_5667187] using wordTrace_append hprefix tailTrace_5667187
  have hstable : (prefixWord ++ tailWord_5667187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667187).length < 2 ^ (prefixWord ++ tailWord_5667187).sum := by decide
  have hdescent : baseEnd_5667187 < baseStart_5667187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667201 : List Nat := [1, 2, 4, 3, 1, 1, 4, 7]
def baseStart_5667201 : Nat := 118140960795 + 5667201 * 2 ^ 59
def prefixEnd_5667201 : Nat := 4983230072969 + 3 ^ 40 * 5667201 * 2
def baseEnd_5667201 : Nat := 107777706616332843841649

theorem tailTrace_5667201 : CollatzResearch.WordTrace tailWord_5667201 prefixEnd_5667201 107777706616332843841649 := by
  unfold tailWord_5667201
  simp only [CollatzResearch.WordTrace]
  refine ⟨206699801541706132718977457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137799867694470755145984971 206699801541706132718977457)
  ·
    refine ⟨155024851156279599539233093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206699801541706132718977457 155024851156279599539233093)
    ·
      refine ⟨29067159591802424913606205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155024851156279599539233093 29067159591802424913606205)
      ·
        refine ⟨10900184846925909342602327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29067159591802424913606205 10900184846925909342602327)
        ·
          refine ⟨16350277270388864013903491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10900184846925909342602327 16350277270388864013903491)
          ·
            refine ⟨24525415905583296020855237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16350277270388864013903491 24525415905583296020855237)
            ·
              refine ⟨4598515482296868003910357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24525415905583296020855237 4598515482296868003910357)
              ·
                refine ⟨107777706616332843841649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4598515482296868003910357 107777706616332843841649)
                ·
                  rfl

theorem cell23_5667201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 4, 7].length) (baseStart_5667201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667201 prefixEnd_5667201 := by exact prefixLift 5667201
  have htrace : WordTrace (prefixWord ++ tailWord_5667201) baseStart_5667201 baseEnd_5667201 := by
    simpa [prefixWord, tailWord_5667201, baseEnd_5667201] using wordTrace_append hprefix tailTrace_5667201
  have hstable : (prefixWord ++ tailWord_5667201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667201).length < 2 ^ (prefixWord ++ tailWord_5667201).sum := by decide
  have hdescent : baseEnd_5667201 < baseStart_5667201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667211 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 4, 1, 3]
def baseStart_5667211 : Nat := 118140960795 + 5667211 * 2 ^ 59
def prefixEnd_5667211 : Nat := 4983230072969 + 3 ^ 40 * 5667211 * 2
def baseEnd_5667211 : Nat := 2910003213447531744599477

theorem tailTrace_5667211 : CollatzResearch.WordTrace tailWord_5667211 prefixEnd_5667211 2910003213447531744599477 := by
  unfold tailWord_5667211
  simp only [CollatzResearch.WordTrace]
  refine ⟨206700166271669904426841487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137800110847779936284560991 206700166271669904426841487)
  ·
    refine ⟨310050249407504856640262231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206700166271669904426841487 310050249407504856640262231)
    ·
      refine ⟨465075374111257284960393347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310050249407504856640262231 465075374111257284960393347)
      ·
        refine ⟨697613061166885927440590021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465075374111257284960393347 697613061166885927440590021)
        ·
          refine ⟨130802448968791111395110629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 697613061166885927440590021 130802448968791111395110629)
          ·
            refine ⟨24525459181648333386583243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130802448968791111395110629 24525459181648333386583243)
            ·
              refine ⟨36788188772472500079874865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24525459181648333386583243 36788188772472500079874865)
              ·
                refine ⟨27591141579354375059906149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36788188772472500079874865 27591141579354375059906149)
                ·
                  refine ⟨5173339046128945323732403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27591141579354375059906149 5173339046128945323732403)
                  ·
                    refine ⟨7760008569193417985598605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5173339046128945323732403 7760008569193417985598605)
                    ·
                      refine ⟨2910003213447531744599477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7760008569193417985598605 2910003213447531744599477)
                      ·
                        rfl

theorem cell23_5667211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 1, 3].length) (baseStart_5667211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667211 prefixEnd_5667211 := by exact prefixLift 5667211
  have htrace : WordTrace (prefixWord ++ tailWord_5667211) baseStart_5667211 baseEnd_5667211 := by
    simpa [prefixWord, tailWord_5667211, baseEnd_5667211] using wordTrace_append hprefix tailTrace_5667211
  have hstable : (prefixWord ++ tailWord_5667211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667211).length < 2 ^ (prefixWord ++ tailWord_5667211).sum := by decide
  have hdescent : baseEnd_5667211 < baseStart_5667211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667212 : List Nat := [2, 2, 1, 2, 1, 6, 1, 3, 1, 2, 2]
def baseStart_5667212 : Nat := 118140960795 + 5667212 * 2 ^ 59
def prefixEnd_5667212 : Nat := 4983230072969 + 3 ^ 40 * 5667212 * 2
def baseEnd_5667212 : Nat := 2910003726928186240686973

theorem tailTrace_5667212 : CollatzResearch.WordTrace tailWord_5667212 prefixEnd_5667212 2910003726928186240686973 := by
  unfold tailWord_5667212
  simp only [CollatzResearch.WordTrace]
  refine ⟨103350101372333140798813945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137800135163110854398418593 103350101372333140798813945)
  ·
    refine ⟨77512576029249855599110459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103350101372333140798813945 77512576029249855599110459)
    ·
      refine ⟨116268864043874783398665689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77512576029249855599110459 116268864043874783398665689)
      ·
        refine ⟨87201648032906087548999267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116268864043874783398665689 87201648032906087548999267)
        ·
          refine ⟨130802472049359131323498901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87201648032906087548999267 130802472049359131323498901)
          ·
            refine ⟨6131365877313709280789011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 130802472049359131323498901 6131365877313709280789011)
            ·
              refine ⟨9197048815970563921183517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6131365877313709280789011 9197048815970563921183517)
              ·
                refine ⟨3448893305988961470443819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9197048815970563921183517 3448893305988961470443819)
                ·
                  refine ⟨5173339958983442205665729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3448893305988961470443819 5173339958983442205665729)
                  ·
                    refine ⟨3880004969237581654249297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5173339958983442205665729 3880004969237581654249297)
                    ·
                      refine ⟨2910003726928186240686973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3880004969237581654249297 2910003726928186240686973)
                      ·
                        rfl

theorem cell23_5667212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_5667212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667212 prefixEnd_5667212 := by exact prefixLift 5667212
  have htrace : WordTrace (prefixWord ++ tailWord_5667212) baseStart_5667212 baseEnd_5667212 := by
    simpa [prefixWord, tailWord_5667212, baseEnd_5667212] using wordTrace_append hprefix tailTrace_5667212
  have hstable : (prefixWord ++ tailWord_5667212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667212).length < 2 ^ (prefixWord ++ tailWord_5667212).sum := by decide
  have hdescent : baseEnd_5667212 < baseStart_5667212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667221 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 5, 3, 2]
def baseStart_5667221 : Nat := 118140960795 + 5667221 * 2 ^ 59
def prefixEnd_5667221 : Nat := 4983230072969 + 3 ^ 40 * 5667221 * 2
def baseEnd_5667221 : Nat := 2910008348254076705474431

theorem tailTrace_5667221 : CollatzResearch.WordTrace tailWord_5667221 prefixEnd_5667221 2910008348254076705474431 := by
  unfold tailWord_5667221
  simp only [CollatzResearch.WordTrace]
  refine ⟨206700531001633676134705517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137800354001089117423137011 206700531001633676134705517)
  ·
    refine ⟨77512699125612628550514569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206700531001633676134705517 77512699125612628550514569)
    ·
      refine ⟨58134524344209471412885927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77512699125612628550514569 58134524344209471412885927)
      ·
        refine ⟨87201786516314207119328891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58134524344209471412885927 87201786516314207119328891)
        ·
          refine ⟨130802679774471310678993337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87201786516314207119328891 130802679774471310678993337)
          ·
            refine ⟨98102009830853483009245003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130802679774471310678993337 98102009830853483009245003)
            ·
              refine ⟨147153014746280224513867505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98102009830853483009245003 147153014746280224513867505)
              ·
                refine ⟨110364761059710168385400629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147153014746280224513867505 110364761059710168385400629)
                ·
                  refine ⟨10346696349347828286131309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110364761059710168385400629 10346696349347828286131309)
                  ·
                    refine ⟨3880011131005435607299241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10346696349347828286131309 3880011131005435607299241)
                    ·
                      refine ⟨2910008348254076705474431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3880011131005435607299241 2910008348254076705474431)
                      ·
                        rfl

theorem cell23_5667221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 3, 2].length) (baseStart_5667221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667221 prefixEnd_5667221 := by exact prefixLift 5667221
  have htrace : WordTrace (prefixWord ++ tailWord_5667221) baseStart_5667221 baseEnd_5667221 := by
    simpa [prefixWord, tailWord_5667221, baseEnd_5667221] using wordTrace_append hprefix tailTrace_5667221
  have hstable : (prefixWord ++ tailWord_5667221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667221).length < 2 ^ (prefixWord ++ tailWord_5667221).sum := by decide
  have hdescent : baseEnd_5667221 < baseStart_5667221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667227 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 2, 12]
def baseStart_5667227 : Nat := 118140960795 + 5667227 * 2 ^ 59
def prefixEnd_5667227 : Nat := 4983230072969 + 3 ^ 40 * 5667227 * 2
def baseEnd_5667227 : Nat := 970003809712667893999801

theorem tailTrace_5667227 : CollatzResearch.WordTrace tailWord_5667227 prefixEnd_5667227 970003809712667893999801 := by
  unfold tailWord_5667227
  simp only [CollatzResearch.WordTrace]
  refine ⟨206700749839611939159423935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137800499893074626106282623 206700749839611939159423935)
  ·
    refine ⟨310051124759417908739135903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206700749839611939159423935 310051124759417908739135903)
    ·
      refine ⟨465076687139126863108703855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310051124759417908739135903 465076687139126863108703855)
      ·
        refine ⟨697615030708690294663055783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465076687139126863108703855 697615030708690294663055783)
        ·
          refine ⟨1046422546063035441994583675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697615030708690294663055783 1046422546063035441994583675)
          ·
            refine ⟨1569633819094553162991875513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046422546063035441994583675 1569633819094553162991875513)
            ·
              refine ⟨1177225364320914872243906635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1569633819094553162991875513 1177225364320914872243906635)
              ·
                refine ⟨1765838046481372308365859953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1177225364320914872243906635 1765838046481372308365859953)
                ·
                  refine ⟨1324378534861029231274394965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1765838046481372308365859953 1324378534861029231274394965)
                  ·
                    refine ⟨970003809712667893999801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1324378534861029231274394965 970003809712667893999801)
                    ·
                      rfl

theorem cell23_5667227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 12].length) (baseStart_5667227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667227 prefixEnd_5667227 := by exact prefixLift 5667227
  have htrace : WordTrace (prefixWord ++ tailWord_5667227) baseStart_5667227 baseEnd_5667227 := by
    simpa [prefixWord, tailWord_5667227, baseEnd_5667227] using wordTrace_append hprefix tailTrace_5667227
  have hstable : (prefixWord ++ tailWord_5667227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667227).length < 2 ^ (prefixWord ++ tailWord_5667227).sum := by decide
  have hdescent : baseEnd_5667227 < baseStart_5667227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667229 : List Nat := [1, 4, 2, 1, 4, 1, 3, 2, 1, 2, 2]
def baseStart_5667229 : Nat := 118140960795 + 5667229 * 2 ^ 59
def prefixEnd_5667229 : Nat := 4983230072969 + 3 ^ 40 * 5667229 * 2
def baseEnd_5667229 : Nat := 2910012456099312674174395

theorem tailTrace_5667229 : CollatzResearch.WordTrace tailWord_5667229 prefixEnd_5667229 2910012456099312674174395 := by
  unfold tailWord_5667229
  simp only [CollatzResearch.WordTrace]
  refine ⟨206700822785604693500996741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137800548523736462333997827 206700822785604693500996741)
  ·
    refine ⟨38756404272300880031436889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206700822785604693500996741 38756404272300880031436889)
    ·
      refine ⟨29067303204225660023577667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38756404272300880031436889 29067303204225660023577667)
      ·
        refine ⟨43600954806338490035366501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29067303204225660023577667 43600954806338490035366501)
        ·
          refine ⟨8175179026188466881631219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43600954806338490035366501 8175179026188466881631219)
          ·
            refine ⟨12262768539282700322446829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8175179026188466881631219 12262768539282700322446829)
            ·
              refine ⟨4598538202231012620917561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12262768539282700322446829 4598538202231012620917561)
              ·
                refine ⟨3448903651673259465688171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4598538202231012620917561 3448903651673259465688171)
                ·
                  refine ⟨5173355477509889198532257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3448903651673259465688171 5173355477509889198532257)
                  ·
                    refine ⟨3880016608132416898899193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5173355477509889198532257 3880016608132416898899193)
                    ·
                      refine ⟨2910012456099312674174395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3880016608132416898899193 2910012456099312674174395)
                      ·
                        rfl

theorem cell23_5667229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_5667229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667229 prefixEnd_5667229 := by exact prefixLift 5667229
  have htrace : WordTrace (prefixWord ++ tailWord_5667229) baseStart_5667229 baseEnd_5667229 := by
    simpa [prefixWord, tailWord_5667229, baseEnd_5667229] using wordTrace_append hprefix tailTrace_5667229
  have hstable : (prefixWord ++ tailWord_5667229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667229).length < 2 ^ (prefixWord ++ tailWord_5667229).sum := by decide
  have hdescent : baseEnd_5667229 < baseStart_5667229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667255 : List Nat := [1, 1, 3, 1, 3, 5, 1, 2, 1, 3, 2]
def baseStart_5667255 : Nat := 118140960795 + 5667255 * 2 ^ 59
def prefixEnd_5667255 : Nat := 4983230072969 + 3 ^ 40 * 5667255 * 2
def baseEnd_5667255 : Nat := 2910025806596329572449275

theorem tailTrace_5667255 : CollatzResearch.WordTrace tailWord_5667255 prefixEnd_5667255 2910025806596329572449275 := by
  unfold tailWord_5667255
  simp only [CollatzResearch.WordTrace]
  refine ⟨206701771083510499941443219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137801180722340333294295479 206701771083510499941443219)
  ·
    refine ⟨310052656625265749912164829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206701771083510499941443219 310052656625265749912164829)
    ·
      refine ⟨116269746234474656217061811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310052656625265749912164829 116269746234474656217061811)
      ·
        refine ⟨174404619351711984325592717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116269746234474656217061811 174404619351711984325592717)
        ·
          refine ⟨65401732256891994122097269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174404619351711984325592717 65401732256891994122097269)
          ·
            refine ⟨6131412399083624448946619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65401732256891994122097269 6131412399083624448946619)
            ·
              refine ⟨9197118598625436673419929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6131412399083624448946619 9197118598625436673419929)
              ·
                refine ⟨6897838948969077505064947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9197118598625436673419929 6897838948969077505064947)
                ·
                  refine ⟨10346758423453616257597421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6897838948969077505064947 10346758423453616257597421)
                  ·
                    refine ⟨3880034408795106096599033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10346758423453616257597421 3880034408795106096599033)
                    ·
                      refine ⟨2910025806596329572449275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3880034408795106096599033 2910025806596329572449275)
                      ·
                        rfl

theorem cell23_5667255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 3, 2].length) (baseStart_5667255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667255 prefixEnd_5667255 := by exact prefixLift 5667255
  have htrace : WordTrace (prefixWord ++ tailWord_5667255) baseStart_5667255 baseEnd_5667255 := by
    simpa [prefixWord, tailWord_5667255, baseEnd_5667255] using wordTrace_append hprefix tailTrace_5667255
  have hstable : (prefixWord ++ tailWord_5667255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667255).length < 2 ^ (prefixWord ++ tailWord_5667255).sum := by decide
  have hdescent : baseEnd_5667255 < baseStart_5667255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667264 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 4]
def baseStart_5667264 : Nat := 118140960795 + 5667264 * 2 ^ 59
def prefixEnd_5667264 : Nat := 4983230072969 + 3 ^ 40 * 5667264 * 2
def baseEnd_5667264 : Nat := 2910030427922220037236733

theorem tailTrace_5667264 : CollatzResearch.WordTrace tailWord_5667264 prefixEnd_5667264 2910030427922220037236733 := by
  unfold tailWord_5667264
  simp only [CollatzResearch.WordTrace]
  refine ⟨103351049670238947239260423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137801399560318596319013897 103351049670238947239260423)
  ·
    refine ⟨155026574505358420858890635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103351049670238947239260423 155026574505358420858890635)
    ·
      refine ⟨232539861758037631288335953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155026574505358420858890635 232539861758037631288335953)
      ·
        refine ⟨174404896318528223466251965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232539861758037631288335953 174404896318528223466251965)
        ·
          refine ⟨65401836119448083799844487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174404896318528223466251965 65401836119448083799844487)
          ·
            refine ⟨98102754179172125699766731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65401836119448083799844487 98102754179172125699766731)
            ·
              refine ⟨147154131268758188549650097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98102754179172125699766731 147154131268758188549650097)
              ·
                refine ⟨110365598451568641412237573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147154131268758188549650097 110365598451568641412237573)
                ·
                  refine ⟨20693549709669120264794545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110365598451568641412237573 20693549709669120264794545)
                  ·
                    refine ⟨15520162282251840198595909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20693549709669120264794545 15520162282251840198595909)
                    ·
                      refine ⟨2910030427922220037236733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15520162282251840198595909 2910030427922220037236733)
                      ·
                        rfl

theorem cell23_5667264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_5667264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667264 prefixEnd_5667264 := by exact prefixLift 5667264
  have htrace : WordTrace (prefixWord ++ tailWord_5667264) baseStart_5667264 baseEnd_5667264 := by
    simpa [prefixWord, tailWord_5667264, baseEnd_5667264] using wordTrace_append hprefix tailTrace_5667264
  have hstable : (prefixWord ++ tailWord_5667264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667264).length < 2 ^ (prefixWord ++ tailWord_5667264).sum := by decide
  have hdescent : baseEnd_5667264 < baseStart_5667264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667285 : List Nat := [1, 3, 2, 3, 1, 2, 1, 4, 2, 2, 2]
def baseStart_5667285 : Nat := 118140960795 + 5667285 * 2 ^ 59
def prefixEnd_5667285 : Nat := 4983230072969 + 3 ^ 40 * 5667285 * 2
def baseEnd_5667285 : Nat := 2910041211015964455074137

theorem tailTrace_5667285 : CollatzResearch.WordTrace tailWord_5667285 prefixEnd_5667285 2910041211015964455074137 := by
  unfold tailWord_5667285
  simp only [CollatzResearch.WordTrace]
  refine ⟨206702865273401815065035309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137801910182267876710023539 206702865273401815065035309)
  ·
    refine ⟨77513574477525680649388241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206702865273401815065035309 77513574477525680649388241)
    ·
      refine ⟨58135180858144260487041181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77513574477525680649388241 58135180858144260487041181)
      ·
        refine ⟨21800692821804097682640443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58135180858144260487041181 21800692821804097682640443)
        ·
          refine ⟨32701039232706146523960665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21800692821804097682640443 32701039232706146523960665)
          ·
            refine ⟨24525779424529609892970499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32701039232706146523960665 24525779424529609892970499)
            ·
              refine ⟨36788669136794414839455749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24525779424529609892970499 36788669136794414839455749)
              ·
                refine ⟨6897875463148952782397953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36788669136794414839455749 6897875463148952782397953)
                ·
                  refine ⟨5173406597361714586798465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6897875463148952782397953 5173406597361714586798465)
                  ·
                    refine ⟨3880054948021285940098849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5173406597361714586798465 3880054948021285940098849)
                    ·
                      refine ⟨2910041211015964455074137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3880054948021285940098849 2910041211015964455074137)
                      ·
                        rfl

theorem cell23_5667285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_5667285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667285 prefixEnd_5667285 := by exact prefixLift 5667285
  have htrace : WordTrace (prefixWord ++ tailWord_5667285) baseStart_5667285 baseEnd_5667285 := by
    simpa [prefixWord, tailWord_5667285, baseEnd_5667285] using wordTrace_append hprefix tailTrace_5667285
  have hstable : (prefixWord ++ tailWord_5667285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667285).length < 2 ^ (prefixWord ++ tailWord_5667285).sum := by decide
  have hdescent : baseEnd_5667285 < baseStart_5667285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667311 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 4, 5, 2]
def baseStart_5667311 : Nat := 118140960795 + 5667311 * 2 ^ 59
def prefixEnd_5667311 : Nat := 4983230072969 + 3 ^ 40 * 5667311 * 2
def baseEnd_5667311 : Nat := 2910054561512981353349017

theorem tailTrace_5667311 : CollatzResearch.WordTrace tailWord_5667311 prefixEnd_5667311 2910054561512981353349017 := by
  unfold tailWord_5667311
  simp only [CollatzResearch.WordTrace]
  refine ⟨206703813571307621505481787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137802542380871747670321191 206703813571307621505481787)
  ·
    refine ⟨310055720356961432258222681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206703813571307621505481787 310055720356961432258222681)
    ·
      refine ⟨232541790267721074193667011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310055720356961432258222681 232541790267721074193667011)
      ·
        refine ⟨348812685401581611290500517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232541790267721074193667011 348812685401581611290500517)
        ·
          refine ⟨65402378512796552116968847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 348812685401581611290500517 65402378512796552116968847)
          ·
            refine ⟨98103567769194828175453271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65402378512796552116968847 98103567769194828175453271)
            ·
              refine ⟨147155351653792242263179907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98103567769194828175453271 147155351653792242263179907)
              ·
                refine ⟨220733027480688363394769861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147155351653792242263179907 220733027480688363394769861)
                ·
                  refine ⟨41387442652629068136519349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220733027480688363394769861 41387442652629068136519349)
                  ·
                    refine ⟨3880072748683975137798689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41387442652629068136519349 3880072748683975137798689)
                    ·
                      refine ⟨2910054561512981353349017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3880072748683975137798689 2910054561512981353349017)
                      ·
                        rfl

theorem cell23_5667311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 5, 2].length) (baseStart_5667311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667311 prefixEnd_5667311 := by exact prefixLift 5667311
  have htrace : WordTrace (prefixWord ++ tailWord_5667311) baseStart_5667311 baseEnd_5667311 := by
    simpa [prefixWord, tailWord_5667311, baseEnd_5667311] using wordTrace_append hprefix tailTrace_5667311
  have hstable : (prefixWord ++ tailWord_5667311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667311).length < 2 ^ (prefixWord ++ tailWord_5667311).sum := by decide
  have hdescent : baseEnd_5667311 < baseStart_5667311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667321 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 2, 5]
def baseStart_5667321 : Nat := 118140960795 + 5667321 * 2 ^ 59
def prefixEnd_5667321 : Nat := 4983230072969 + 3 ^ 40 * 5667321 * 2
def baseEnd_5667321 : Nat := 970019898773175438074657

theorem tailTrace_5667321 : CollatzResearch.WordTrace tailWord_5667321 prefixEnd_5667321 970019898773175438074657 := by
  unfold tailWord_5667321
  simp only [CollatzResearch.WordTrace]
  refine ⟨206704178301271393213345817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137802785534180928808897211 206704178301271393213345817)
  ·
    refine ⟨155028133725953544910009363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206704178301271393213345817 155028133725953544910009363)
    ·
      refine ⟨232542200588930317365014045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155028133725953544910009363 232542200588930317365014045)
      ·
        refine ⟨87203325220848869011880267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232542200588930317365014045 87203325220848869011880267)
        ·
          refine ⟨130804987831273303517820401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87203325220848869011880267 130804987831273303517820401)
          ·
            refine ⟨98103740873454977638365301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130804987831273303517820401 98103740873454977638365301)
            ·
              refine ⟨9197225706886404153596747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98103740873454977638365301 9197225706886404153596747)
              ·
                refine ⟨13795838560329606230395121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9197225706886404153596747 13795838560329606230395121)
                ·
                  refine ⟨10346878920247204672796341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13795838560329606230395121 10346878920247204672796341)
                  ·
                    refine ⟨970019898773175438074657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10346878920247204672796341 970019898773175438074657)
                    ·
                      rfl

theorem cell23_5667321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 5].length) (baseStart_5667321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667321 prefixEnd_5667321 := by exact prefixLift 5667321
  have htrace : WordTrace (prefixWord ++ tailWord_5667321) baseStart_5667321 baseEnd_5667321 := by
    simpa [prefixWord, tailWord_5667321, baseEnd_5667321] using wordTrace_append hprefix tailTrace_5667321
  have hstable : (prefixWord ++ tailWord_5667321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667321).length < 2 ^ (prefixWord ++ tailWord_5667321).sum := by decide
  have hdescent : baseEnd_5667321 < baseStart_5667321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667361 : List Nat := [1, 2, 3, 2, 2, 1, 1, 1, 3, 4, 3]
def baseStart_5667361 : Nat := 118140960795 + 5667361 * 2 ^ 59
def prefixEnd_5667361 : Nat := 4983230072969 + 3 ^ 40 * 5667361 * 2
def baseEnd_5667361 : Nat := 2910080235545706157723787

theorem tailTrace_5667361 : CollatzResearch.WordTrace tailWord_5667361 prefixEnd_5667361 2910080235545706157723787 := by
  unfold tailWord_5667361
  simp only [CollatzResearch.WordTrace]
  refine ⟨206705637221126480044801937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137803758147417653363201291 206705637221126480044801937)
  ·
    refine ⟨155029227915844860033601453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206705637221126480044801937 155029227915844860033601453)
    ·
      refine ⟨58135960468441822512600545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155029227915844860033601453 58135960468441822512600545)
      ·
        refine ⟨43601970351331366884450409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58135960468441822512600545 43601970351331366884450409)
        ·
          refine ⟨32701477763498525163337807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43601970351331366884450409 32701477763498525163337807)
          ·
            refine ⟨49052216645247787745006711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32701477763498525163337807 49052216645247787745006711)
            ·
              refine ⟨73578324967871681617510067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49052216645247787745006711 73578324967871681617510067)
              ·
                refine ⟨110367487451807522426265101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73578324967871681617510067 110367487451807522426265101)
                ·
                  refine ⟨41387807794427820909849413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110367487451807522426265101 41387807794427820909849413)
                  ·
                    refine ⟨7760213961455216420596765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41387807794427820909849413 7760213961455216420596765)
                    ·
                      refine ⟨2910080235545706157723787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7760213961455216420596765 2910080235545706157723787)
                      ·
                        rfl

theorem cell23_5667361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_5667361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667361 prefixEnd_5667361 := by exact prefixLift 5667361
  have htrace : WordTrace (prefixWord ++ tailWord_5667361) baseStart_5667361 baseEnd_5667361 := by
    simpa [prefixWord, tailWord_5667361, baseEnd_5667361] using wordTrace_append hprefix tailTrace_5667361
  have hstable : (prefixWord ++ tailWord_5667361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667361).length < 2 ^ (prefixWord ++ tailWord_5667361).sum := by decide
  have hdescent : baseEnd_5667361 < baseStart_5667361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667402 : List Nat := [3, 1, 2, 1, 1, 5, 3, 2, 1, 4]
def baseStart_5667402 : Nat := 118140960795 + 5667402 * 2 ^ 59
def prefixEnd_5667402 : Nat := 4983230072969 + 3 ^ 40 * 5667402 * 2
def baseEnd_5667402 : Nat := 970033762750846832437033

theorem tailTrace_5667402 : CollatzResearch.WordTrace tailWord_5667402 prefixEnd_5667402 970033762750846832437033 := by
  unfold tailWord_5667402
  simp only [CollatzResearch.WordTrace]
  refine ⟨51676783153494486011761115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137804755075985296031362973 51676783153494486011761115)
  ·
    refine ⟨77515174730241729017641673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51676783153494486011761115 77515174730241729017641673)
    ·
      refine ⟨58136381047681296763231255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77515174730241729017641673 58136381047681296763231255)
      ·
        refine ⟨87204571571521945144846883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58136381047681296763231255 87204571571521945144846883)
        ·
          refine ⟨130806857357282917717270325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87204571571521945144846883 130806857357282917717270325)
          ·
            refine ⟨12263142877245273535994093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 130806857357282917717270325 12263142877245273535994093)
            ·
              refine ⟨4598678578966977575997785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12263142877245273535994093 4598678578966977575997785)
              ·
                refine ⟨3449008934225233181998339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4598678578966977575997785 3449008934225233181998339)
                ·
                  refine ⟨5173513401337849772997509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3449008934225233181998339 5173513401337849772997509)
                  ·
                    refine ⟨970033762750846832437033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5173513401337849772997509 970033762750846832437033)
                    ·
                      rfl

theorem cell23_5667402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 1, 4].length) (baseStart_5667402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667402 prefixEnd_5667402 := by exact prefixLift 5667402
  have htrace : WordTrace (prefixWord ++ tailWord_5667402) baseStart_5667402 baseEnd_5667402 := by
    simpa [prefixWord, tailWord_5667402, baseEnd_5667402] using wordTrace_append hprefix tailTrace_5667402
  have hstable : (prefixWord ++ tailWord_5667402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667402).length < 2 ^ (prefixWord ++ tailWord_5667402).sum := by decide
  have hdescent : baseEnd_5667402 < baseStart_5667402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667408 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 3, 1, 3]
def baseStart_5667408 : Nat := 118140960795 + 5667408 * 2 ^ 59
def prefixEnd_5667408 : Nat := 4983230072969 + 3 ^ 40 * 5667408 * 2
def baseEnd_5667408 : Nat := 2910104369136467473836071

theorem tailTrace_5667408 : CollatzResearch.WordTrace tailWord_5667408 prefixEnd_5667408 2910104369136467473836071 := by
  unfold tailWord_5667408
  simp only [CollatzResearch.WordTrace]
  refine ⟨103353675725978103535881439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137804900967970804714508585 103353675725978103535881439)
  ·
    refine ⟨155030513588967155303822159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103353675725978103535881439 155030513588967155303822159)
    ·
      refine ⟨232545770383450732955733239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155030513588967155303822159 232545770383450732955733239)
      ·
        refine ⟨348818655575176099433599859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232545770383450732955733239 348818655575176099433599859)
        ·
          refine ⟨523227983362764149150399789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348818655575176099433599859 523227983362764149150399789)
          ·
            refine ⟨196210493761036555931399921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 523227983362764149150399789 196210493761036555931399921)
            ·
              refine ⟨147157870320777416948549941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196210493761036555931399921 147157870320777416948549941)
              ·
                refine ⟨13796050342572882838926557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147157870320777416948549941 13796050342572882838926557)
                ·
                  refine ⟨5173518878464831064597459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13796050342572882838926557 5173518878464831064597459)
                  ·
                    refine ⟨7760278317697246596896189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5173518878464831064597459 7760278317697246596896189)
                    ·
                      refine ⟨2910104369136467473836071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7760278317697246596896189 2910104369136467473836071)
                      ·
                        rfl

theorem cell23_5667408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 3, 1, 3].length) (baseStart_5667408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667408 prefixEnd_5667408 := by exact prefixLift 5667408
  have htrace : WordTrace (prefixWord ++ tailWord_5667408) baseStart_5667408 baseEnd_5667408 := by
    simpa [prefixWord, tailWord_5667408, baseEnd_5667408] using wordTrace_append hprefix tailTrace_5667408
  have hstable : (prefixWord ++ tailWord_5667408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667408).length < 2 ^ (prefixWord ++ tailWord_5667408).sum := by decide
  have hdescent : baseEnd_5667408 < baseStart_5667408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667451 : List Nat := [1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 5]
def baseStart_5667451 : Nat := 118140960795 + 5667451 * 2 ^ 59
def prefixEnd_5667451 : Nat := 4983230072969 + 3 ^ 40 * 5667451 * 2
def baseEnd_5667451 : Nat := 2910126448804610805598373

theorem tailTrace_5667451 : CollatzResearch.WordTrace tailWord_5667451 prefixEnd_5667451 2910126448804610805598373 := by
  unfold tailWord_5667451
  simp only [CollatzResearch.WordTrace]
  refine ⟨206708919790800425415578207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137805946527200283610385471 206708919790800425415578207)
  ·
    refine ⟨310063379686200638123367311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206708919790800425415578207 310063379686200638123367311)
    ·
      refine ⟨465095069529300957185050967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310063379686200638123367311 465095069529300957185050967)
      ·
        refine ⟨697642604293951435777576451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465095069529300957185050967 697642604293951435777576451)
        ·
          refine ⟨1046463906440927153666364677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697642604293951435777576451 1046463906440927153666364677)
          ·
            refine ⟨196211982457673841312443377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1046463906440927153666364677 196211982457673841312443377)
            ·
              refine ⟨147158986843255380984332533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196211982457673841312443377 147158986843255380984332533)
              ·
                refine ⟨13796155016555191967281175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147158986843255380984332533 13796155016555191967281175)
                ·
                  refine ⟨20694232524832787950921763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13796155016555191967281175 20694232524832787950921763)
                  ·
                    refine ⟨31041348787249181926382645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20694232524832787950921763 31041348787249181926382645)
                    ·
                      refine ⟨2910126448804610805598373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31041348787249181926382645 2910126448804610805598373)
                      ·
                        rfl

theorem cell23_5667451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 5].length) (baseStart_5667451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667451 prefixEnd_5667451 := by exact prefixLift 5667451
  have htrace : WordTrace (prefixWord ++ tailWord_5667451) baseStart_5667451 baseEnd_5667451 := by
    simpa [prefixWord, tailWord_5667451, baseEnd_5667451] using wordTrace_append hprefix tailTrace_5667451
  have hstable : (prefixWord ++ tailWord_5667451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667451).length < 2 ^ (prefixWord ++ tailWord_5667451).sum := by decide
  have hdescent : baseEnd_5667451 < baseStart_5667451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667465 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 3, 2, 2]
def baseStart_5667465 : Nat := 118140960795 + 5667465 * 2 ^ 59
def prefixEnd_5667465 : Nat := 4983230072969 + 3 ^ 40 * 5667465 * 2
def baseEnd_5667465 : Nat := 2910133637533773750823309

theorem tailTrace_5667465 : CollatzResearch.WordTrace tailWord_5667465 prefixEnd_5667465 2910133637533773750823309 := by
  unfold tailWord_5667465
  simp only [CollatzResearch.WordTrace]
  refine ⟨206709430412749705806587849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137806286941833137204391899 206709430412749705806587849)
  ·
    refine ⟨155032072809562279354940887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206709430412749705806587849 155032072809562279354940887)
    ·
      refine ⟨232548109214343419032411331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155032072809562279354940887 232548109214343419032411331)
      ·
        refine ⟨348822163821515128548616997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232548109214343419032411331 348822163821515128548616997)
        ·
          refine ⟨65404155716534086602865687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 348822163821515128548616997 65404155716534086602865687)
          ·
            refine ⟨98106233574801129904298531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65404155716534086602865687 98106233574801129904298531)
            ·
              refine ⟨147159350362201694856447797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98106233574801129904298531 147159350362201694856447797)
              ·
                refine ⟨13796189096456408892791981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147159350362201694856447797 13796189096456408892791981)
                ·
                  refine ⟨5173570911171153334796993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13796189096456408892791981 5173570911171153334796993)
                  ·
                    refine ⟨3880178183378365001097745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5173570911171153334796993 3880178183378365001097745)
                    ·
                      refine ⟨2910133637533773750823309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3880178183378365001097745 2910133637533773750823309)
                      ·
                        rfl

theorem cell23_5667465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 2, 2].length) (baseStart_5667465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667465 prefixEnd_5667465 := by exact prefixLift 5667465
  have htrace : WordTrace (prefixWord ++ tailWord_5667465) baseStart_5667465 baseEnd_5667465 := by
    simpa [prefixWord, tailWord_5667465, baseEnd_5667465] using wordTrace_append hprefix tailTrace_5667465
  have hstable : (prefixWord ++ tailWord_5667465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667465).length < 2 ^ (prefixWord ++ tailWord_5667465).sum := by decide
  have hdescent : baseEnd_5667465 < baseStart_5667465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667526 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_5667526 : Nat := 118140960795 + 5667526 * 2 ^ 59
def prefixEnd_5667526 : Nat := 4983230072969 + 3 ^ 40 * 5667526 * 2
def baseEnd_5667526 : Nat := 970054986617899337386843

theorem tailTrace_5667526 : CollatzResearch.WordTrace tailWord_5667526 prefixEnd_5667526 970054986617899337386843 := by
  unfold tailWord_5667526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6459739227047772288267451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 137807770177019142149705621 6459739227047772288267451)
  ·
    refine ⟨9689608840571658432401177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6459739227047772288267451 9689608840571658432401177)
    ·
      refine ⟨7267206630428743824300883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9689608840571658432401177 7267206630428743824300883)
      ·
        refine ⟨10900809945643115736451325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7267206630428743824300883 10900809945643115736451325)
        ·
          refine ⟨4087803729616168401169247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10900809945643115736451325 4087803729616168401169247)
          ·
            refine ⟨6131705594424252601753871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4087803729616168401169247 6131705594424252601753871)
            ·
              refine ⟨9197558391636378902630807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6131705594424252601753871 9197558391636378902630807)
              ·
                refine ⟨13796337587454568353946211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9197558391636378902630807 13796337587454568353946211)
                ·
                  refine ⟨20694506381181852530919317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13796337587454568353946211 20694506381181852530919317)
                  ·
                    refine ⟨970054986617899337386843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20694506381181852530919317 970054986617899337386843)
                    ·
                      rfl

theorem cell23_5667526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_5667526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667526 prefixEnd_5667526 := by exact prefixLift 5667526
  have htrace : WordTrace (prefixWord ++ tailWord_5667526) baseStart_5667526 baseEnd_5667526 := by
    simpa [prefixWord, tailWord_5667526, baseEnd_5667526] using wordTrace_append hprefix tailTrace_5667526
  have hstable : (prefixWord ++ tailWord_5667526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667526).length < 2 ^ (prefixWord ++ tailWord_5667526).sum := by decide
  have hdescent : baseEnd_5667526 < baseStart_5667526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667532 : List Nat := [2, 2, 1, 5, 1, 3, 1, 1, 1, 3, 3]
def baseStart_5667532 : Nat := 118140960795 + 5667532 * 2 ^ 59
def prefixEnd_5667532 : Nat := 4983230072969 + 3 ^ 40 * 5667532 * 2
def baseEnd_5667532 : Nat := 2910168040737624988685501

theorem tailTrace_5667532 : CollatzResearch.WordTrace tailWord_5667532 prefixEnd_5667532 2910168040737624988685501 := by
  unfold tailWord_5667532
  simp only [CollatzResearch.WordTrace]
  refine ⟨103355937051753488124638425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137807916069004650832851233 103355937051753488124638425)
  ·
    refine ⟨77516952788815116093478819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103355937051753488124638425 77516952788815116093478819)
    ·
      refine ⟨116275429183222674140218229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77516952788815116093478819 116275429183222674140218229)
      ·
        refine ⟨10900821485927125700645459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116275429183222674140218229 10900821485927125700645459)
        ·
          refine ⟨16351232228890688550968189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10900821485927125700645459 16351232228890688550968189)
          ·
            refine ⟨6131712085834008206613071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16351232228890688550968189 6131712085834008206613071)
            ·
              refine ⟨9197568128751012309919607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6131712085834008206613071 9197568128751012309919607)
              ·
                refine ⟨13796352193126518464879411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9197568128751012309919607 13796352193126518464879411)
                ·
                  refine ⟨20694528289689777697319117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13796352193126518464879411 20694528289689777697319117)
                  ·
                    refine ⟨7760448108633666636494669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20694528289689777697319117 7760448108633666636494669)
                    ·
                      refine ⟨2910168040737624988685501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7760448108633666636494669 2910168040737624988685501)
                      ·
                        rfl

theorem cell23_5667532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_5667532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667532 prefixEnd_5667532 := by exact prefixLift 5667532
  have htrace : WordTrace (prefixWord ++ tailWord_5667532) baseStart_5667532 baseEnd_5667532 := by
    simpa [prefixWord, tailWord_5667532, baseEnd_5667532] using wordTrace_append hprefix tailTrace_5667532
  have hstable : (prefixWord ++ tailWord_5667532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667532).length < 2 ^ (prefixWord ++ tailWord_5667532).sum := by decide
  have hdescent : baseEnd_5667532 < baseStart_5667532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667561 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 9]
def baseStart_5667561 : Nat := 118140960795 + 5667561 * 2 ^ 59
def prefixEnd_5667561 : Nat := 4983230072969 + 3 ^ 40 * 5667561 * 2
def baseEnd_5667561 : Nat := 323353659075178375024763

theorem tailTrace_5667561 : CollatzResearch.WordTrace tailWord_5667561 prefixEnd_5667561 323353659075178375024763 := by
  unfold tailWord_5667561
  simp only [CollatzResearch.WordTrace]
  refine ⟨206712931820401914202082537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137808621213601276134721691 206712931820401914202082537)
  ·
    refine ⟨155034698865301435651561903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206712931820401914202082537 155034698865301435651561903)
    ·
      refine ⟨232552048297952153477342855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155034698865301435651561903 232552048297952153477342855)
      ·
        refine ⟨348828072446928230216014283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232552048297952153477342855 348828072446928230216014283)
        ·
          refine ⟨523242108670392345324021425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348828072446928230216014283 523242108670392345324021425)
          ·
            refine ⟨392431581502794258993016069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 523242108670392345324021425 392431581502794258993016069)
            ·
              refine ⟨73580921531773923561190513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 392431581502794258993016069 73580921531773923561190513)
              ·
                refine ⟨55185691148830442670892885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73580921531773923561190513 55185691148830442670892885)
                ·
                  refine ⟨323353659075178375024763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55185691148830442670892885 323353659075178375024763)
                  ·
                    rfl

theorem cell23_5667561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 9].length) (baseStart_5667561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667561 prefixEnd_5667561 := by exact prefixLift 5667561
  have htrace : WordTrace (prefixWord ++ tailWord_5667561) baseStart_5667561 baseEnd_5667561 := by
    simpa [prefixWord, tailWord_5667561, baseEnd_5667561] using wordTrace_append hprefix tailTrace_5667561
  have hstable : (prefixWord ++ tailWord_5667561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667561).length < 2 ^ (prefixWord ++ tailWord_5667561).sum := by decide
  have hdescent : baseEnd_5667561 < baseStart_5667561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667571 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 9]
def baseStart_5667571 : Nat := 118140960795 + 5667571 * 2 ^ 59
def prefixEnd_5667571 : Nat := 4983230072969 + 3 ^ 40 * 5667571 * 2
def baseEnd_5667571 : Nat := 2910188066483150336097821

theorem tailTrace_5667571 : CollatzResearch.WordTrace tailWord_5667571 prefixEnd_5667571 2910188066483150336097821 := by
  unfold tailWord_5667571
  simp only [CollatzResearch.WordTrace]
  refine ⟨206713296550365685909946567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137808864366910457273297711 206713296550365685909946567)
  ·
    refine ⟨310069944825548528864919851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206713296550365685909946567 310069944825548528864919851)
    ·
      refine ⟨465104917238322793297379777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310069944825548528864919851 465104917238322793297379777)
      ·
        refine ⟨348828687928742094973034833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465104917238322793297379777 348828687928742094973034833)
        ·
          refine ⟨261621515946556571229776125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 348828687928742094973034833 261621515946556571229776125)
          ·
            refine ⟨98108068479958714211166047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261621515946556571229776125 98108068479958714211166047)
            ·
              refine ⟨147162102719938071316749071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98108068479958714211166047 147162102719938071316749071)
              ·
                refine ⟨220743154079907106975123607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147162102719938071316749071 220743154079907106975123607)
                ·
                  refine ⟨331114731119860660462685411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220743154079907106975123607 331114731119860660462685411)
                  ·
                    refine ⟨496672096679790990694028117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 331114731119860660462685411 496672096679790990694028117)
                    ·
                      refine ⟨2910188066483150336097821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 496672096679790990694028117 2910188066483150336097821)
                      ·
                        rfl

theorem cell23_5667571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_5667571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667571 prefixEnd_5667571 := by exact prefixLift 5667571
  have htrace : WordTrace (prefixWord ++ tailWord_5667571) baseStart_5667571 baseEnd_5667571 := by
    simpa [prefixWord, tailWord_5667571, baseEnd_5667571] using wordTrace_append hprefix tailTrace_5667571
  have hstable : (prefixWord ++ tailWord_5667571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667571).length < 2 ^ (prefixWord ++ tailWord_5667571).sum := by decide
  have hdescent : baseEnd_5667571 < baseStart_5667571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667578 : List Nat := [3, 1, 1, 1, 1, 3, 5, 1, 7]
def baseStart_5667578 : Nat := 118140960795 + 5667578 * 2 ^ 59
def prefixEnd_5667578 : Nat := 4983230072969 + 3 ^ 40 * 5667578 * 2
def baseEnd_5667578 : Nat := 323354628983081312078921

theorem tailTrace_5667578 : CollatzResearch.WordTrace tailWord_5667578 prefixEnd_5667578 323354628983081312078921 := by
  unfold tailWord_5667578
  simp only [CollatzResearch.WordTrace]
  refine ⟨51678387965335081526362847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137809034574226884070300925 51678387965335081526362847)
  ·
    refine ⟨77517581948002622289544271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51678387965335081526362847 77517581948002622289544271)
    ·
      refine ⟨116276372922003933434316407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77517581948002622289544271 116276372922003933434316407)
      ·
        refine ⟨174414559383005900151474611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116276372922003933434316407 174414559383005900151474611)
        ·
          refine ⟨261621839074508850227211917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174414559383005900151474611 261621839074508850227211917)
          ·
            refine ⟨98108189652940818835204469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261621839074508850227211917 98108189652940818835204469)
            ·
              refine ⟨9197642779963201765800419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98108189652940818835204469 9197642779963201765800419)
              ·
                refine ⟨13796464169944802648700629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9197642779963201765800419 13796464169944802648700629)
                ·
                  refine ⟨323354628983081312078921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13796464169944802648700629 323354628983081312078921)
                  ·
                    rfl

theorem cell23_5667578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 7].length) (baseStart_5667578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667578 prefixEnd_5667578 := by exact prefixLift 5667578
  have htrace : WordTrace (prefixWord ++ tailWord_5667578) baseStart_5667578 baseEnd_5667578 := by
    simpa [prefixWord, tailWord_5667578, baseEnd_5667578] using wordTrace_append hprefix tailTrace_5667578
  have hstable : (prefixWord ++ tailWord_5667578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667578).length < 2 ^ (prefixWord ++ tailWord_5667578).sum := by decide
  have hdescent : baseEnd_5667578 < baseStart_5667578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667658 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_5667658 : Nat := 118140960795 + 5667658 * 2 ^ 59
def prefixEnd_5667658 : Nat := 4983230072969 + 3 ^ 40 * 5667658 * 2
def baseEnd_5667658 : Nat := 2910232739300091495709921

theorem tailTrace_5667658 : CollatzResearch.WordTrace tailWord_5667658 prefixEnd_5667658 2910232739300091495709921 := by
  unfold tailWord_5667658
  simp only [CollatzResearch.WordTrace]
  refine ⟨51679117425262624942090907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137810979800700333178909085 51679117425262624942090907)
  ·
    refine ⟨77518676137893937413136361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51679117425262624942090907 77518676137893937413136361)
    ·
      refine ⟨58139007103420453059852271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77518676137893937413136361 58139007103420453059852271)
      ·
        refine ⟨87208510655130679589778407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58139007103420453059852271 87208510655130679589778407)
        ·
          refine ⟨130812765982696019384667611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87208510655130679589778407 130812765982696019384667611)
          ·
            refine ⟨196219148974044029077001417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130812765982696019384667611 196219148974044029077001417)
            ·
              refine ⟨147164361730533021807751063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196219148974044029077001417 147164361730533021807751063)
              ·
                refine ⟨220746542595799532711626595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147164361730533021807751063 220746542595799532711626595)
                ·
                  refine ⟨331119813893699299067439893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220746542595799532711626595 331119813893699299067439893)
                  ·
                    refine ⟨15521241276267154643786245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 331119813893699299067439893 15521241276267154643786245)
                    ·
                      refine ⟨2910232739300091495709921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15521241276267154643786245 2910232739300091495709921)
                      ·
                        rfl

theorem cell23_5667658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_5667658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667658 prefixEnd_5667658 := by exact prefixLift 5667658
  have htrace : WordTrace (prefixWord ++ tailWord_5667658) baseStart_5667658 baseEnd_5667658 := by
    simpa [prefixWord, tailWord_5667658, baseEnd_5667658] using wordTrace_append hprefix tailTrace_5667658
  have hstable : (prefixWord ++ tailWord_5667658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667658).length < 2 ^ (prefixWord ++ tailWord_5667658).sum := by decide
  have hdescent : baseEnd_5667658 < baseStart_5667658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667685 : List Nat := [1, 3, 1, 3, 1, 1, 5, 2, 6]
def baseStart_5667685 : Nat := 118140960795 + 5667685 * 2 ^ 59
def prefixEnd_5667685 : Nat := 4983230072969 + 3 ^ 40 * 5667685 * 2
def baseEnd_5667685 : Nat := 323360733697529210008033

theorem tailTrace_5667685 : CollatzResearch.WordTrace tailWord_5667685 prefixEnd_5667685 323360733697529210008033 := by
  unfold tailWord_5667685
  simp only [CollatzResearch.WordTrace]
  refine ⟨206717454471952683379596509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137811636314635122253064339 206717454471952683379596509)
  ·
    refine ⟨77519045426982256267348691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206717454471952683379596509 77519045426982256267348691)
    ·
      refine ⟨116278568140473384401023037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77519045426982256267348691 116278568140473384401023037)
      ·
        refine ⟨43604463052677519150383639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116278568140473384401023037 43604463052677519150383639)
        ·
          refine ⟨65406694579016278725575459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43604463052677519150383639 65406694579016278725575459)
          ·
            refine ⟨98110041868524418088363189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65406694579016278725575459 98110041868524418088363189)
            ·
              refine ⟨9197816425174164195784049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98110041868524418088363189 9197816425174164195784049)
              ·
                refine ⟨6898362318880623146838037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9197816425174164195784049 6898362318880623146838037)
                ·
                  refine ⟨323360733697529210008033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6898362318880623146838037 323360733697529210008033)
                  ·
                    rfl

theorem cell23_5667685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 2, 6].length) (baseStart_5667685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667685 prefixEnd_5667685 := by exact prefixLift 5667685
  have htrace : WordTrace (prefixWord ++ tailWord_5667685) baseStart_5667685 baseEnd_5667685 := by
    simpa [prefixWord, tailWord_5667685, baseEnd_5667685] using wordTrace_append hprefix tailTrace_5667685
  have hstable : (prefixWord ++ tailWord_5667685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667685).length < 2 ^ (prefixWord ++ tailWord_5667685).sum := by decide
  have hdescent : baseEnd_5667685 < baseStart_5667685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667708 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_5667708 : Nat := 118140960795 + 5667708 * 2 ^ 59
def prefixEnd_5667708 : Nat := 4983230072969 + 3 ^ 40 * 5667708 * 2
def baseEnd_5667708 : Nat := 2910258413332816300084691

theorem tailTrace_5667708 : CollatzResearch.WordTrace tailWord_5667708 prefixEnd_5667708 2910258413332816300084691 := by
  unfold tailWord_5667708
  simp only [CollatzResearch.WordTrace]
  refine ⟨103359146675434679153841889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137812195567246238871789185 103359146675434679153841889)
  ·
    refine ⟨77519360006576009365381417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103359146675434679153841889 77519360006576009365381417)
    ·
      refine ⟨58139520004932007024036063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77519360006576009365381417 58139520004932007024036063)
      ·
        refine ⟨87209280007398010536054095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58139520004932007024036063 87209280007398010536054095)
        ·
          refine ⟨130813920011097015804081143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87209280007398010536054095 130813920011097015804081143)
          ·
            refine ⟨196220880016645523706121715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130813920011097015804081143 196220880016645523706121715)
            ·
              refine ⟨294331320024968285559182573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196220880016645523706121715 294331320024968285559182573)
              ·
                refine ⟨110374245009363107084693465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 294331320024968285559182573 110374245009363107084693465)
                ·
                  refine ⟨82780683757022330313520099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110374245009363107084693465 82780683757022330313520099)
                  ·
                    refine ⟨124171025635533495470280149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82780683757022330313520099 124171025635533495470280149)
                    ·
                      refine ⟨2910258413332816300084691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124171025635533495470280149 2910258413332816300084691)
                      ·
                        rfl

theorem cell23_5667708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_5667708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667708 prefixEnd_5667708 := by exact prefixLift 5667708
  have htrace : WordTrace (prefixWord ++ tailWord_5667708) baseStart_5667708 baseEnd_5667708 := by
    simpa [prefixWord, tailWord_5667708, baseEnd_5667708] using wordTrace_append hprefix tailTrace_5667708
  have hstable : (prefixWord ++ tailWord_5667708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667708).length < 2 ^ (prefixWord ++ tailWord_5667708).sum := by decide
  have hdescent : baseEnd_5667708 < baseStart_5667708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667732 : List Nat := [2, 4, 2, 1, 1, 1, 1, 5, 1, 5]
def baseStart_5667732 : Nat := 118140960795 + 5667732 * 2 ^ 59
def prefixEnd_5667732 : Nat := 4983230072969 + 3 ^ 40 * 5667732 * 2
def baseEnd_5667732 : Nat := 970090245622841402061527

theorem tailTrace_5667732 : CollatzResearch.WordTrace tailWord_5667732 prefixEnd_5667732 970090245622841402061527 := by
  unfold tailWord_5667732
  simp only [CollatzResearch.WordTrace]
  refine ⟨103359584351391205203278725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137812779135188273604371633 103359584351391205203278725)
  ·
    refine ⟨19379922065885850975614761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103359584351391205203278725 19379922065885850975614761)
    ·
      refine ⟨14534941549414388231711071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19379922065885850975614761 14534941549414388231711071)
      ·
        refine ⟨21802412324121582347566607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14534941549414388231711071 21802412324121582347566607)
        ·
          refine ⟨32703618486182373521349911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21802412324121582347566607 32703618486182373521349911)
          ·
            refine ⟨49055427729273560282024867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32703618486182373521349911 49055427729273560282024867)
            ·
              refine ⟨73583141593910340423037301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49055427729273560282024867 73583141593910340423037301)
              ·
                refine ⟨6898419524429094414659747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73583141593910340423037301 6898419524429094414659747)
                ·
                  refine ⟨10347629286643641621989621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6898419524429094414659747 10347629286643641621989621)
                  ·
                    refine ⟨970090245622841402061527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10347629286643641621989621 970090245622841402061527)
                    ·
                      rfl

theorem cell23_5667732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_5667732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667732 prefixEnd_5667732 := by exact prefixLift 5667732
  have htrace : WordTrace (prefixWord ++ tailWord_5667732) baseStart_5667732 baseEnd_5667732 := by
    simpa [prefixWord, tailWord_5667732, baseEnd_5667732] using wordTrace_append hprefix tailTrace_5667732
  have hstable : (prefixWord ++ tailWord_5667732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667732).length < 2 ^ (prefixWord ++ tailWord_5667732).sum := by decide
  have hdescent : baseEnd_5667732 < baseStart_5667732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667746 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_5667746 : Nat := 118140960795 + 5667746 * 2 ^ 59
def prefixEnd_5667746 : Nat := 4983230072969 + 3 ^ 40 * 5667746 * 2
def baseEnd_5667746 : Nat := 2910277925597687151409517

theorem tailTrace_5667746 : CollatzResearch.WordTrace tailWord_5667746 prefixEnd_5667746 2910277925597687151409517 := by
  unfold tailWord_5667746
  simp only [CollatzResearch.WordTrace]
  refine ⟨51679919831182922699391773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137813119549821127198378061 51679919831182922699391773)
  ·
    refine ⟨19379969936693596012271915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51679919831182922699391773 19379969936693596012271915)
    ·
      refine ⟨29069954905040394018407873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19379969936693596012271915 29069954905040394018407873)
      ·
        refine ⟨21802466178780295513805905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29069954905040394018407873 21802466178780295513805905)
        ·
          refine ⟨16351849634085221635354429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21802466178780295513805905 16351849634085221635354429)
          ·
            refine ⟨6131943612781958113257911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16351849634085221635354429 6131943612781958113257911)
            ·
              refine ⟨9197915419172937169886867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6131943612781958113257911 9197915419172937169886867)
              ·
                refine ⟨13796873128759405754830301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9197915419172937169886867 13796873128759405754830301)
                ·
                  refine ⟨5173827423284777158061363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13796873128759405754830301 5173827423284777158061363)
                  ·
                    refine ⟨7760741134927165737092045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5173827423284777158061363 7760741134927165737092045)
                    ·
                      refine ⟨2910277925597687151409517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7760741134927165737092045 2910277925597687151409517)
                      ·
                        rfl

theorem cell23_5667746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_5667746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667746 prefixEnd_5667746 := by exact prefixLift 5667746
  have htrace : WordTrace (prefixWord ++ tailWord_5667746) baseStart_5667746 baseEnd_5667746 := by
    simpa [prefixWord, tailWord_5667746, baseEnd_5667746] using wordTrace_append hprefix tailTrace_5667746
  have hstable : (prefixWord ++ tailWord_5667746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667746).length < 2 ^ (prefixWord ++ tailWord_5667746).sum := by decide
  have hdescent : baseEnd_5667746 < baseStart_5667746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667755 : List Nat := [1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 3]
def baseStart_5667755 : Nat := 118140960795 + 5667755 * 2 ^ 59
def prefixEnd_5667755 : Nat := 4983230072969 + 3 ^ 40 * 5667755 * 2
def baseEnd_5667755 : Nat := 2910282546923577616196975

theorem tailTrace_5667755 : CollatzResearch.WordTrace tailWord_5667755 prefixEnd_5667755 2910282546923577616196975 := by
  unfold tailWord_5667755
  simp only [CollatzResearch.WordTrace]
  refine ⟨206720007581699085334644719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137813338387799390223096479 206720007581699085334644719)
  ·
    refine ⟨310080011372548628001967079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206720007581699085334644719 310080011372548628001967079)
    ·
      refine ⟨465120017058822942002950619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310080011372548628001967079 465120017058822942002950619)
      ·
        refine ⟨697680025588234413004425929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465120017058822942002950619 697680025588234413004425929)
        ·
          refine ⟨523260019191175809753319447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697680025588234413004425929 523260019191175809753319447)
          ·
            refine ⟨784890028786763714629979171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523260019191175809753319447 784890028786763714629979171)
            ·
              refine ⟨1177335043180145571944968757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784890028786763714629979171 1177335043180145571944968757)
              ·
                refine ⟨110375160298138647369840821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1177335043180145571944968757 110375160298138647369840821)
                ·
                  refine ⟨10347671277950498190922577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110375160298138647369840821 10347671277950498190922577)
                  ·
                    refine ⟨7760753458462873643191933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10347671277950498190922577 7760753458462873643191933)
                    ·
                      refine ⟨2910282546923577616196975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7760753458462873643191933 2910282546923577616196975)
                      ·
                        rfl

theorem cell23_5667755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 3].length) (baseStart_5667755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667755 prefixEnd_5667755 := by exact prefixLift 5667755
  have htrace : WordTrace (prefixWord ++ tailWord_5667755) baseStart_5667755 baseEnd_5667755 := by
    simpa [prefixWord, tailWord_5667755, baseEnd_5667755] using wordTrace_append hprefix tailTrace_5667755
  have hstable : (prefixWord ++ tailWord_5667755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667755).length < 2 ^ (prefixWord ++ tailWord_5667755).sum := by decide
  have hdescent : baseEnd_5667755 < baseStart_5667755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667765 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 1, 1, 6]
def baseStart_5667765 : Nat := 118140960795 + 5667765 * 2 ^ 59
def prefixEnd_5667765 : Nat := 4983230072969 + 3 ^ 40 * 5667765 * 2
def baseEnd_5667765 : Nat := 2910287681730122577071929

theorem tailTrace_5667765 : CollatzResearch.WordTrace tailWord_5667765 prefixEnd_5667765 2910287681730122577071929 := by
  unfold tailWord_5667765
  simp only [CollatzResearch.WordTrace]
  refine ⟨206720372311662857042508749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137813581541108571361672499 206720372311662857042508749)
  ·
    refine ⟨77520139616873571390940781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206720372311662857042508749 77520139616873571390940781)
    ·
      refine ⟨29070052356327589271602793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77520139616873571390940781 29070052356327589271602793)
      ·
        refine ⟨21802539267245691953702095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29070052356327589271602793 21802539267245691953702095)
        ·
          refine ⟨32703808900868537930553143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21802539267245691953702095 32703808900868537930553143)
          ·
            refine ⟨49055713351302806895829715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32703808900868537930553143 49055713351302806895829715)
            ·
              refine ⟨73583570026954210343744573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49055713351302806895829715 73583570026954210343744573)
              ·
                refine ⟨27593838760107828878904215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73583570026954210343744573 27593838760107828878904215)
                ·
                  refine ⟨41390758140161743318356323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27593838760107828878904215 41390758140161743318356323)
                  ·
                    refine ⟨62086137210242614977534485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41390758140161743318356323 62086137210242614977534485)
                    ·
                      refine ⟨2910287681730122577071929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62086137210242614977534485 2910287681730122577071929)
                      ·
                        rfl

theorem cell23_5667765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_5667765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667765 prefixEnd_5667765 := by exact prefixLift 5667765
  have htrace : WordTrace (prefixWord ++ tailWord_5667765) baseStart_5667765 baseEnd_5667765 := by
    simpa [prefixWord, tailWord_5667765, baseEnd_5667765] using wordTrace_append hprefix tailTrace_5667765
  have hstable : (prefixWord ++ tailWord_5667765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667765).length < 2 ^ (prefixWord ++ tailWord_5667765).sum := by decide
  have hdescent : baseEnd_5667765 < baseStart_5667765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667769 : List Nat := [1, 2, 1, 4, 2, 4, 1, 2, 1, 1, 4]
def baseStart_5667769 : Nat := 118140960795 + 5667769 * 2 ^ 59
def prefixEnd_5667769 : Nat := 4983230072969 + 3 ^ 40 * 5667769 * 2
def baseEnd_5667769 : Nat := 2910289735652740561421911

theorem tailTrace_5667769 : CollatzResearch.WordTrace tailWord_5667769 prefixEnd_5667769 2910289735652740561421911 := by
  unfold tailWord_5667769
  simp only [CollatzResearch.WordTrace]
  refine ⟨206720518203648365725654361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137813678802432243817102907 206720518203648365725654361)
  ·
    refine ⟨155040388652736274294240771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206720518203648365725654361 155040388652736274294240771)
    ·
      refine ⟨232560582979104411441361157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155040388652736274294240771 232560582979104411441361157)
      ·
        refine ⟨43605109308582077145255217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232560582979104411441361157 43605109308582077145255217)
        ·
          refine ⟨32703831981436557858941413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43605109308582077145255217 32703831981436557858941413)
          ·
            refine ⟨6131968496519354598551515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32703831981436557858941413 6131968496519354598551515)
            ·
              refine ⟨9197952744779031897827273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6131968496519354598551515 9197952744779031897827273)
              ·
                refine ⟨6898464558584273923370455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9197952744779031897827273 6898464558584273923370455)
                ·
                  refine ⟨10347696837876410885055683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6898464558584273923370455 10347696837876410885055683)
                  ·
                    refine ⟨15521545256814616327583525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10347696837876410885055683 15521545256814616327583525)
                    ·
                      refine ⟨2910289735652740561421911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15521545256814616327583525 2910289735652740561421911)
                      ·
                        rfl

theorem cell23_5667769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_5667769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667769 prefixEnd_5667769 := by exact prefixLift 5667769
  have htrace : WordTrace (prefixWord ++ tailWord_5667769) baseStart_5667769 baseEnd_5667769 := by
    simpa [prefixWord, tailWord_5667769, baseEnd_5667769] using wordTrace_append hprefix tailTrace_5667769
  have hstable : (prefixWord ++ tailWord_5667769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667769).length < 2 ^ (prefixWord ++ tailWord_5667769).sum := by decide
  have hdescent : baseEnd_5667769 < baseStart_5667769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667786 : List Nat := [3, 1, 2, 1, 2, 1, 1, 7, 1, 2, 2]
def baseStart_5667786 : Nat := 118140960795 + 5667786 * 2 ^ 59
def prefixEnd_5667786 : Nat := 4983230072969 + 3 ^ 40 * 5667786 * 2
def baseEnd_5667786 : Nat := 2910298464823866994909333

theorem tailTrace_5667786 : CollatzResearch.WordTrace tailWord_5667786 prefixEnd_5667786 2910298464823866994909333 := by
  unfold tailWord_5667786
  simp only [CollatzResearch.WordTrace]
  refine ⟨51680284561146694407255803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137814092163057851752682141 51680284561146694407255803)
  ·
    refine ⟨77520426841720041610883705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51680284561146694407255803 77520426841720041610883705)
    ·
      refine ⟨58140320131290031208162779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77520426841720041610883705 58140320131290031208162779)
      ·
        refine ⟨87210480196935046812244169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58140320131290031208162779 87210480196935046812244169)
        ·
          refine ⟨65407860147701285109183127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87210480196935046812244169 65407860147701285109183127)
          ·
            refine ⟨98111790221551927663774691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65407860147701285109183127 98111790221551927663774691)
            ·
              refine ⟨147167685332327891495662037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98111790221551927663774691 147167685332327891495662037)
              ·
                refine ⟨3449242624976434956929579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 147167685332327891495662037 3449242624976434956929579)
                ·
                  refine ⟨5173863937464652435394369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3449242624976434956929579 5173863937464652435394369)
                  ·
                    refine ⟨3880397953098489326545777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5173863937464652435394369 3880397953098489326545777)
                    ·
                      refine ⟨2910298464823866994909333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3880397953098489326545777 2910298464823866994909333)
                      ·
                        rfl

theorem cell23_5667786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_5667786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667786 prefixEnd_5667786 := by exact prefixLift 5667786
  have htrace : WordTrace (prefixWord ++ tailWord_5667786) baseStart_5667786 baseEnd_5667786 := by
    simpa [prefixWord, tailWord_5667786, baseEnd_5667786] using wordTrace_append hprefix tailTrace_5667786
  have hstable : (prefixWord ++ tailWord_5667786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667786).length < 2 ^ (prefixWord ++ tailWord_5667786).sum := by decide
  have hdescent : baseEnd_5667786 < baseStart_5667786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667845 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 1, 3, 5]
def baseStart_5667845 : Nat := 118140960795 + 5667845 * 2 ^ 59
def prefixEnd_5667845 : Nat := 4983230072969 + 3 ^ 40 * 5667845 * 2
def baseEnd_5667845 : Nat := 2910328760182482264071561

theorem tailTrace_5667845 : CollatzResearch.WordTrace tailWord_5667845 prefixEnd_5667845 2910328760182482264071561 := by
  unfold tailWord_5667845
  simp only [CollatzResearch.WordTrace]
  refine ⟨206723290151373030705420989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137815526767582020470280659 206723290151373030705420989)
  ·
    refine ⟨77521233806764886514532871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206723290151373030705420989 77521233806764886514532871)
    ·
      refine ⟨116281850710147329771799307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77521233806764886514532871 116281850710147329771799307)
      ·
        refine ⟨174422776065220994657698961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116281850710147329771799307 174422776065220994657698961)
        ·
          refine ⟨130817082048915745993274221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174422776065220994657698961 130817082048915745993274221)
          ·
            refine ⟨49056405768343404747477833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130817082048915745993274221 49056405768343404747477833)
            ·
              refine ⟨36792304326257553560608375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49056405768343404747477833 36792304326257553560608375)
              ·
                refine ⟨55188456489386330340912563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36792304326257553560608375 55188456489386330340912563)
                ·
                  refine ⟨82782684734079495511368845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55188456489386330340912563 82782684734079495511368845)
                  ·
                    refine ⟨31043506775279810816763317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82782684734079495511368845 31043506775279810816763317)
                    ·
                      refine ⟨2910328760182482264071561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31043506775279810816763317 2910328760182482264071561)
                      ·
                        rfl

theorem cell23_5667845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_5667845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667845 prefixEnd_5667845 := by exact prefixLift 5667845
  have htrace : WordTrace (prefixWord ++ tailWord_5667845) baseStart_5667845 baseEnd_5667845 := by
    simpa [prefixWord, tailWord_5667845, baseEnd_5667845] using wordTrace_append hprefix tailTrace_5667845
  have hstable : (prefixWord ++ tailWord_5667845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667845).length < 2 ^ (prefixWord ++ tailWord_5667845).sum := by decide
  have hdescent : baseEnd_5667845 < baseStart_5667845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667865 : List Nat := [1, 2, 1, 2, 1, 1, 5, 3, 7]
def baseStart_5667865 : Nat := 118140960795 + 5667865 * 2 ^ 59
def prefixEnd_5667865 : Nat := 4983230072969 + 3 ^ 40 * 5667865 * 2
def baseEnd_5667865 : Nat := 323371003310619131757941

theorem tailTrace_5667865 : CollatzResearch.WordTrace tailWord_5667865 prefixEnd_5667865 323371003310619131757941 := by
  unfold tailWord_5667865
  simp only [CollatzResearch.WordTrace]
  refine ⟨206724019611300574121149049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137816013074200382747432699 206724019611300574121149049)
  ·
    refine ⟨155043014708475430590861787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206724019611300574121149049 155043014708475430590861787)
    ·
      refine ⟨232564522062713145886292681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155043014708475430590861787 232564522062713145886292681)
      ·
        refine ⟨174423391547034859414719511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232564522062713145886292681 174423391547034859414719511)
        ·
          refine ⟨261635087320552289122079267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174423391547034859414719511 261635087320552289122079267)
          ·
            refine ⟨392452630980828433683118901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261635087320552289122079267 392452630980828433683118901)
            ·
              refine ⟨36792434154452665657792397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 392452630980828433683118901 36792434154452665657792397)
              ·
                refine ⟨13797162807919749621672149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36792434154452665657792397 13797162807919749621672149)
                ·
                  refine ⟨323371003310619131757941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13797162807919749621672149 323371003310619131757941)
                  ·
                    rfl

theorem cell23_5667865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 3, 7].length) (baseStart_5667865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667865 prefixEnd_5667865 := by exact prefixLift 5667865
  have htrace : WordTrace (prefixWord ++ tailWord_5667865) baseStart_5667865 baseEnd_5667865 := by
    simpa [prefixWord, tailWord_5667865, baseEnd_5667865] using wordTrace_append hprefix tailTrace_5667865
  have hstable : (prefixWord ++ tailWord_5667865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667865).length < 2 ^ (prefixWord ++ tailWord_5667865).sum := by decide
  have hdescent : baseEnd_5667865 < baseStart_5667865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667876 : List Nat := [2, 3, 1, 4, 1, 1, 3, 1, 1, 4, 2]
def baseStart_5667876 : Nat := 118140960795 + 5667876 * 2 ^ 59
def prefixEnd_5667876 : Nat := 4983230072969 + 3 ^ 40 * 5667876 * 2
def baseEnd_5667876 : Nat := 2910344678082771642783919

theorem tailTrace_5667876 : CollatzResearch.WordTrace tailWord_5667876 prefixEnd_5667876 2910344678082771642783919 := by
  unfold tailWord_5667876
  simp only [CollatzResearch.WordTrace]
  refine ⟨103362210407130361499899741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137816280542840481999866321 103362210407130361499899741)
  ·
    refine ⟨38760828902673885562462403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103362210407130361499899741 38760828902673885562462403)
    ·
      refine ⟨58141243354010828343693605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38760828902673885562462403 58141243354010828343693605)
      ·
        refine ⟨10901483128877030314442551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58141243354010828343693605 10901483128877030314442551)
        ·
          refine ⟨16352224693315545471663827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10901483128877030314442551 16352224693315545471663827)
          ·
            refine ⟨24528337039973318207495741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16352224693315545471663827 24528337039973318207495741)
            ·
              refine ⟨9198126389989994327810903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24528337039973318207495741 9198126389989994327810903)
              ·
                refine ⟨13797189584984991491716355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9198126389989994327810903 13797189584984991491716355)
                ·
                  refine ⟨20695784377477487237574533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13797189584984991491716355 20695784377477487237574533)
                  ·
                    refine ⟨3880459570777028857045225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20695784377477487237574533 3880459570777028857045225)
                    ·
                      refine ⟨2910344678082771642783919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3880459570777028857045225 2910344678082771642783919)
                      ·
                        rfl

theorem cell23_5667876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_5667876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667876 prefixEnd_5667876 := by exact prefixLift 5667876
  have htrace : WordTrace (prefixWord ++ tailWord_5667876) baseStart_5667876 baseEnd_5667876 := by
    simpa [prefixWord, tailWord_5667876, baseEnd_5667876] using wordTrace_append hprefix tailTrace_5667876
  have hstable : (prefixWord ++ tailWord_5667876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667876).length < 2 ^ (prefixWord ++ tailWord_5667876).sum := by decide
  have hdescent : baseEnd_5667876 < baseStart_5667876 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667912 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 2, 5]
def baseStart_5667912 : Nat := 118140960795 + 5667912 * 2 ^ 59
def prefixEnd_5667912 : Nat := 4983230072969 + 3 ^ 40 * 5667912 * 2
def baseEnd_5667912 : Nat := 970121054462111167311251

theorem tailTrace_5667912 : CollatzResearch.WordTrace tailWord_5667912 prefixEnd_5667912 970121054462111167311251 := by
  unfold tailWord_5667912
  simp only [CollatzResearch.WordTrace]
  refine ⟨103362866921065150574054995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137817155894753534098739993 103362866921065150574054995)
  ·
    refine ⟨155044300381597725861082493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103362866921065150574054995 155044300381597725861082493)
    ·
      refine ⟨58141612643099147197905935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155044300381597725861082493 58141612643099147197905935)
      ·
        refine ⟨87212418964648720796858903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58141612643099147197905935 87212418964648720796858903)
        ·
          refine ⟨130818628446973081195288355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87212418964648720796858903 130818628446973081195288355)
          ·
            refine ⟨196227942670459621792932533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130818628446973081195288355 196227942670459621792932533)
            ·
              refine ⟨18396369625355589543087425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 196227942670459621792932533 18396369625355589543087425)
              ·
                refine ⟨13797277219016692157315569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18396369625355589543087425 13797277219016692157315569)
                ·
                  refine ⟨10347957914262519117986677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13797277219016692157315569 10347957914262519117986677)
                  ·
                    refine ⟨970121054462111167311251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10347957914262519117986677 970121054462111167311251)
                    ·
                      rfl

theorem cell23_5667912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_5667912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667912 prefixEnd_5667912 := by exact prefixLift 5667912
  have htrace : WordTrace (prefixWord ++ tailWord_5667912) baseStart_5667912 baseEnd_5667912 := by
    simpa [prefixWord, tailWord_5667912, baseEnd_5667912] using wordTrace_append hprefix tailTrace_5667912
  have hstable : (prefixWord ++ tailWord_5667912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667912).length < 2 ^ (prefixWord ++ tailWord_5667912).sum := by decide
  have hdescent : baseEnd_5667912 < baseStart_5667912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667922 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_5667922 : Nat := 118140960795 + 5667922 * 2 ^ 59
def prefixEnd_5667922 : Nat := 4983230072969 + 3 ^ 40 * 5667922 * 2
def baseEnd_5667922 : Nat := 2910368298192878462808707

theorem tailTrace_5667922 : CollatzResearch.WordTrace tailWord_5667922 prefixEnd_5667922 2910368298192878462808707 := by
  unfold tailWord_5667922
  simp only [CollatzResearch.WordTrace]
  refine ⟨51681524643023518213993505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137817399048062715237316013 51681524643023518213993505)
  ·
    refine ⟨38761143482267638660495129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51681524643023518213993505 38761143482267638660495129)
    ·
      refine ⟨29070857611700728995371347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38761143482267638660495129 29070857611700728995371347)
      ·
        refine ⟨43606286417551093493057021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29070857611700728995371347 43606286417551093493057021)
        ·
          refine ⟨16352357406581660059896383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43606286417551093493057021 16352357406581660059896383)
          ·
            refine ⟨24528536109872490089844575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16352357406581660059896383 24528536109872490089844575)
            ·
              refine ⟨36792804164808735134766863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24528536109872490089844575 36792804164808735134766863)
              ·
                refine ⟨55189206247213102702150295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36792804164808735134766863 55189206247213102702150295)
                ·
                  refine ⟨82783809370819654053225443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55189206247213102702150295 82783809370819654053225443)
                  ·
                    refine ⟨124175714056229481079838165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82783809370819654053225443 124175714056229481079838165)
                    ·
                      refine ⟨2910368298192878462808707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124175714056229481079838165 2910368298192878462808707)
                      ·
                        rfl

theorem cell23_5667922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_5667922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667922 prefixEnd_5667922 := by exact prefixLift 5667922
  have htrace : WordTrace (prefixWord ++ tailWord_5667922) baseStart_5667922 baseEnd_5667922 := by
    simpa [prefixWord, tailWord_5667922, baseEnd_5667922] using wordTrace_append hprefix tailTrace_5667922
  have hstable : (prefixWord ++ tailWord_5667922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667922).length < 2 ^ (prefixWord ++ tailWord_5667922).sum := by decide
  have hdescent : baseEnd_5667922 < baseStart_5667922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5667949 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_5667949 : Nat := 118140960795 + 5667949 * 2 ^ 59
def prefixEnd_5667949 : Nat := 4983230072969 + 3 ^ 40 * 5667949 * 2
def baseEnd_5667949 : Nat := 2910382162170549857171083

theorem tailTrace_5667949 : CollatzResearch.WordTrace tailWord_5667949 prefixEnd_5667949 2910382162170549857171083 := by
  unfold tailWord_5667949
  simp only [CollatzResearch.WordTrace]
  refine ⟨206727083342996256467206901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137818055561997504311471267 206727083342996256467206901)
  ·
    refine ⟨19380664063405899043800647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206727083342996256467206901 19380664063405899043800647)
    ·
      refine ⟨29070996095108848565700971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19380664063405899043800647 29070996095108848565700971)
      ·
        refine ⟨43606494142663272848551457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29070996095108848565700971 43606494142663272848551457)
        ·
          refine ⟨32704870606997454636413593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43606494142663272848551457 32704870606997454636413593)
          ·
            refine ⟨24528652955248090977310195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32704870606997454636413593 24528652955248090977310195)
            ·
              refine ⟨36792979432872136465965293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24528652955248090977310195 36792979432872136465965293)
              ·
                refine ⟨13797367287327051174736985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36792979432872136465965293 13797367287327051174736985)
                ·
                  refine ⟨10348025465495288381052739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13797367287327051174736985 10348025465495288381052739)
                  ·
                    refine ⟨15522038198242932571579109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10348025465495288381052739 15522038198242932571579109)
                    ·
                      refine ⟨2910382162170549857171083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15522038198242932571579109 2910382162170549857171083)
                      ·
                        rfl

theorem cell23_5667949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_5667949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5667949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5667949 prefixEnd_5667949 := by exact prefixLift 5667949
  have htrace : WordTrace (prefixWord ++ tailWord_5667949) baseStart_5667949 baseEnd_5667949 := by
    simpa [prefixWord, tailWord_5667949, baseEnd_5667949] using wordTrace_append hprefix tailTrace_5667949
  have hstable : (prefixWord ++ tailWord_5667949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5667949).length < 2 ^ (prefixWord ++ tailWord_5667949).sum := by decide
  have hdescent : baseEnd_5667949 < baseStart_5667949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5667949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668009 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 8, 3, 2]
def baseStart_5668009 : Nat := 118140960795 + 5668009 * 2 ^ 59
def prefixEnd_5668009 : Nat := 4983230072969 + 3 ^ 40 * 5668009 * 2
def baseEnd_5668009 : Nat := 2910412971009819622420807

theorem tailTrace_5668009 : CollatzResearch.WordTrace tailWord_5668009 prefixEnd_5668009 2910412971009819622420807 := by
  unfold tailWord_5668009
  simp only [CollatzResearch.WordTrace]
  refine ⟨206729271722778886714391081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137819514481852591142927387 206729271722778886714391081)
  ·
    refine ⟨155046953792084165035793311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206729271722778886714391081 155046953792084165035793311)
    ·
      refine ⟨232570430688126247553689967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155046953792084165035793311 232570430688126247553689967)
      ·
        refine ⟨348855646032189371330534951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232570430688126247553689967 348855646032189371330534951)
        ·
          refine ⟨523283469048284056995802427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348855646032189371330534951 523283469048284056995802427)
          ·
            refine ⟨784925203572426085493703641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523283469048284056995802427 784925203572426085493703641)
            ·
              refine ⟨588693902679319564120277731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784925203572426085493703641 588693902679319564120277731)
              ·
                refine ⟨883040854018979346180416597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588693902679319564120277731 883040854018979346180416597)
                ·
                  refine ⟨10348135008034914213051757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 883040854018979346180416597 10348135008034914213051757)
                  ·
                    refine ⟨3880550628013092829894409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10348135008034914213051757 3880550628013092829894409)
                    ·
                      refine ⟨2910412971009819622420807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3880550628013092829894409 2910412971009819622420807)
                      ·
                        rfl

theorem cell23_5668009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 8, 3, 2].length) (baseStart_5668009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668009 prefixEnd_5668009 := by exact prefixLift 5668009
  have htrace : WordTrace (prefixWord ++ tailWord_5668009) baseStart_5668009 baseEnd_5668009 := by
    simpa [prefixWord, tailWord_5668009, baseEnd_5668009] using wordTrace_append hprefix tailTrace_5668009
  have hstable : (prefixWord ++ tailWord_5668009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668009).length < 2 ^ (prefixWord ++ tailWord_5668009).sum := by decide
  have hdescent : baseEnd_5668009 < baseStart_5668009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668010 : List Nat := [3, 1, 5, 1, 1, 2, 2, 3, 1, 4]
def baseStart_5668010 : Nat := 118140960795 + 5668010 * 2 ^ 59
def prefixEnd_5668010 : Nat := 4983230072969 + 3 ^ 40 * 5668010 * 2
def baseEnd_5668010 : Nat := 970137828163491372836101

theorem tailTrace_5668010 : CollatzResearch.WordTrace tailWord_5668010 prefixEnd_5668010 970137828163491372836101 := by
  unfold tailWord_5668010
  simp only [CollatzResearch.WordTrace]
  refine ⟨51682327048943815971294371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137819538797183509256784989 51682327048943815971294371)
  ·
    refine ⟨77523490573415723956941557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51682327048943815971294371 77523490573415723956941557)
    ·
      refine ⟨7267827241257724120963271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77523490573415723956941557 7267827241257724120963271)
      ·
        refine ⟨10901740861886586181444907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7267827241257724120963271 10901740861886586181444907)
        ·
          refine ⟨16352611292829879272167361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10901740861886586181444907 16352611292829879272167361)
          ·
            refine ⟨12264458469622409454125521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16352611292829879272167361 12264458469622409454125521)
            ·
              refine ⟨9198343852216807090594141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12264458469622409454125521 9198343852216807090594141)
              ·
                refine ⟨3449378944581302658972803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9198343852216807090594141 3449378944581302658972803)
                ·
                  refine ⟨5174068416871953988459205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3449378944581302658972803 5174068416871953988459205)
                  ·
                    refine ⟨970137828163491372836101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5174068416871953988459205 970137828163491372836101)
                    ·
                      rfl

theorem cell23_5668010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_5668010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668010 prefixEnd_5668010 := by exact prefixLift 5668010
  have htrace : WordTrace (prefixWord ++ tailWord_5668010) baseStart_5668010 baseEnd_5668010 := by
    simpa [prefixWord, tailWord_5668010, baseEnd_5668010] using wordTrace_append hprefix tailTrace_5668010
  have hstable : (prefixWord ++ tailWord_5668010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668010).length < 2 ^ (prefixWord ++ tailWord_5668010).sum := by decide
  have hdescent : baseEnd_5668010 < baseStart_5668010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668033 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_5668033 : Nat := 118140960795 + 5668033 * 2 ^ 59
def prefixEnd_5668033 : Nat := 4983230072969 + 3 ^ 40 * 5668033 * 2
def baseEnd_5668033 : Nat := 2910425294545527528520697

theorem tailTrace_5668033 : CollatzResearch.WordTrace tailWord_5668033 prefixEnd_5668033 2910425294545527528520697 := by
  unfold tailWord_5668033
  simp only [CollatzResearch.WordTrace]
  refine ⟨206730147074691938813264753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137820098049794625875509835 206730147074691938813264753)
  ·
    refine ⟨155047610306018954109948565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206730147074691938813264753 155047610306018954109948565)
    ·
      refine ⟨7267856733094638473903839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 155047610306018954109948565 7267856733094638473903839)
      ·
        refine ⟨10901785099641957710855759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7267856733094638473903839 10901785099641957710855759)
        ·
          refine ⟨16352677649462936566283639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10901785099641957710855759 16352677649462936566283639)
          ·
            refine ⟨24529016474194404849425459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16352677649462936566283639 24529016474194404849425459)
            ·
              refine ⟨36793524711291607274138189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24529016474194404849425459 36793524711291607274138189)
              ·
                refine ⟨13797571766734352727801821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36793524711291607274138189 13797571766734352727801821)
                ·
                  refine ⟨5174089412525382272925683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13797571766734352727801821 5174089412525382272925683)
                  ·
                    refine ⟨7761134118788073409388525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5174089412525382272925683 7761134118788073409388525)
                    ·
                      refine ⟨2910425294545527528520697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7761134118788073409388525 2910425294545527528520697)
                      ·
                        rfl

theorem cell23_5668033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_5668033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668033 prefixEnd_5668033 := by exact prefixLift 5668033
  have htrace : WordTrace (prefixWord ++ tailWord_5668033) baseStart_5668033 baseEnd_5668033 := by
    simpa [prefixWord, tailWord_5668033, baseEnd_5668033] using wordTrace_append hprefix tailTrace_5668033
  have hstable : (prefixWord ++ tailWord_5668033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668033).length < 2 ^ (prefixWord ++ tailWord_5668033).sum := by decide
  have hdescent : baseEnd_5668033 < baseStart_5668033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668076 : List Nat := [2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 3]
def baseStart_5668076 : Nat := 118140960795 + 5668076 * 2 ^ 59
def prefixEnd_5668076 : Nat := 4983230072969 + 3 ^ 40 * 5668076 * 2
def baseEnd_5668076 : Nat := 2910447374213670860282999

theorem tailTrace_5668076 : CollatzResearch.WordTrace tailWord_5668076 prefixEnd_5668076 2910447374213670860282999 := by
  unfold tailWord_5668076
  simp only [CollatzResearch.WordTrace]
  refine ⟨103365857706768078578540041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137821143609024104771386721 103365857706768078578540041)
  ·
    refine ⟨77524393280076058933905031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103365857706768078578540041 77524393280076058933905031)
    ·
      refine ⟨116286589920114088400857547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77524393280076058933905031 116286589920114088400857547)
      ·
        refine ⟨174429884880171132601286321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116286589920114088400857547 174429884880171132601286321)
        ·
          refine ⟨130822413660128349450964741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174429884880171132601286321 130822413660128349450964741)
          ·
            refine ⟨24529202561274065522055889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130822413660128349450964741 24529202561274065522055889)
            ·
              refine ⟨18396901920955549141541917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24529202561274065522055889 18396901920955549141541917)
              ·
                refine ⟨6898838220358330928078219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18396901920955549141541917 6898838220358330928078219)
                ·
                  refine ⟨10348257330537496392117329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6898838220358330928078219 10348257330537496392117329)
                  ·
                    refine ⟨7761192997903122294087997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10348257330537496392117329 7761192997903122294087997)
                    ·
                      refine ⟨2910447374213670860282999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7761192997903122294087997 2910447374213670860282999)
                      ·
                        rfl

theorem cell23_5668076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_5668076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668076 prefixEnd_5668076 := by exact prefixLift 5668076
  have htrace : WordTrace (prefixWord ++ tailWord_5668076) baseStart_5668076 baseEnd_5668076 := by
    simpa [prefixWord, tailWord_5668076, baseEnd_5668076] using wordTrace_append hprefix tailTrace_5668076
  have hstable : (prefixWord ++ tailWord_5668076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668076).length < 2 ^ (prefixWord ++ tailWord_5668076).sum := by decide
  have hdescent : baseEnd_5668076 < baseStart_5668076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668079 : List Nat := [1, 1, 2, 1, 7, 2, 9]
def baseStart_5668079 : Nat := 118140960795 + 5668079 * 2 ^ 59
def prefixEnd_5668079 : Nat := 4983230072969 + 3 ^ 40 * 5668079 * 2
def baseEnd_5668079 : Nat := 35931468082168325290685

theorem tailTrace_5668079 : CollatzResearch.WordTrace tailWord_5668079 prefixEnd_5668079 35931468082168325290685 := by
  unfold tailWord_5668079
  simp only [CollatzResearch.WordTrace]
  refine ⟨206731824832525288669439291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137821216555016859112959527 206731824832525288669439291)
  ·
    refine ⟨310097737248787933004158937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206731824832525288669439291 310097737248787933004158937)
    ·
      refine ⟨232573302936590949753119203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310097737248787933004158937 232573302936590949753119203)
      ·
        refine ⟨348859954404886424629678805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232573302936590949753119203 348859954404886424629678805)
        ·
          refine ⟨8176405181364525577258097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 348859954404886424629678805 8176405181364525577258097)
          ·
            refine ⟨6132303886023394182943573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8176405181364525577258097 6132303886023394182943573)
            ·
              refine ⟨35931468082168325290685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6132303886023394182943573 35931468082168325290685)
              ·
                rfl

theorem cell23_5668079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 9].length) (baseStart_5668079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668079 prefixEnd_5668079 := by exact prefixLift 5668079
  have htrace : WordTrace (prefixWord ++ tailWord_5668079) baseStart_5668079 baseEnd_5668079 := by
    simpa [prefixWord, tailWord_5668079, baseEnd_5668079] using wordTrace_append hprefix tailTrace_5668079
  have hstable : (prefixWord ++ tailWord_5668079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668079).length < 2 ^ (prefixWord ++ tailWord_5668079).sum := by decide
  have hdescent : baseEnd_5668079 < baseStart_5668079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668084 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_5668084 : Nat := 118140960795 + 5668084 * 2 ^ 59
def prefixEnd_5668084 : Nat := 4983230072969 + 3 ^ 40 * 5668084 * 2
def baseEnd_5668084 : Nat := 2910451482058906828982963

theorem tailTrace_5668084 : CollatzResearch.WordTrace tailWord_5668084 prefixEnd_5668084 2910451482058906828982963 := by
  unfold tailWord_5668084
  simp only [CollatzResearch.WordTrace]
  refine ⟨103366003598753587261685653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137821338131671449682247537 103366003598753587261685653)
  ·
    refine ⟨4845281418691574402891515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 103366003598753587261685653 4845281418691574402891515)
    ·
      refine ⟨7267922128037361604337273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4845281418691574402891515 7267922128037361604337273)
      ·
        refine ⟨5450941596028021203252955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7267922128037361604337273 5450941596028021203252955)
        ·
          refine ⟨8176412394042031804879433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5450941596028021203252955 8176412394042031804879433)
          ·
            refine ⟨6132309295531523853659575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8176412394042031804879433 6132309295531523853659575)
            ·
              refine ⟨9198463943297285780489363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6132309295531523853659575 9198463943297285780489363)
              ·
                refine ⟨13797695914945928670734045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9198463943297285780489363 13797695914945928670734045)
                ·
                  refine ⟨5174135968104723251525267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13797695914945928670734045 5174135968104723251525267)
                  ·
                    refine ⟨7761203952157084877287901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5174135968104723251525267 7761203952157084877287901)
                    ·
                      refine ⟨2910451482058906828982963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7761203952157084877287901 2910451482058906828982963)
                      ·
                        rfl

theorem cell23_5668084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_5668084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668084 prefixEnd_5668084 := by exact prefixLift 5668084
  have htrace : WordTrace (prefixWord ++ tailWord_5668084) baseStart_5668084 baseEnd_5668084 := by
    simpa [prefixWord, tailWord_5668084, baseEnd_5668084] using wordTrace_append hprefix tailTrace_5668084
  have hstable : (prefixWord ++ tailWord_5668084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668084).length < 2 ^ (prefixWord ++ tailWord_5668084).sum := by decide
  have hdescent : baseEnd_5668084 < baseStart_5668084 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668100 : List Nat := [2, 3, 2, 2, 2, 3, 2, 1, 2, 4]
def baseStart_5668100 : Nat := 118140960795 + 5668100 * 2 ^ 59
def prefixEnd_5668100 : Nat := 4983230072969 + 3 ^ 40 * 5668100 * 2
def baseEnd_5668100 : Nat := 970153232583126255460963

theorem tailTrace_5668100 : CollatzResearch.WordTrace tailWord_5668100 prefixEnd_5668100 970153232583126255460963 := by
  unfold tailWord_5668100
  simp only [CollatzResearch.WordTrace]
  refine ⟨103366295382724604627976877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137821727176966139503969169 103366295382724604627976877)
  ·
    refine ⟨38762360768521726735491329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103366295382724604627976877 38762360768521726735491329)
    ·
      refine ⟨29071770576391295051618497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38762360768521726735491329 29071770576391295051618497)
      ·
        refine ⟨21803827932293471288713873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29071770576391295051618497 21803827932293471288713873)
        ·
          refine ⟨16352870949220103466535405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21803827932293471288713873 16352870949220103466535405)
          ·
            refine ⟨6132326605957538799950777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16352870949220103466535405 6132326605957538799950777)
            ·
              refine ⟨4599244954468154099963083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6132326605957538799950777 4599244954468154099963083)
              ·
                refine ⟨6898867431702231149944625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4599244954468154099963083 6898867431702231149944625)
                ·
                  refine ⟨5174150573776673362458469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6898867431702231149944625 5174150573776673362458469)
                  ·
                    refine ⟨970153232583126255460963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5174150573776673362458469 970153232583126255460963)
                    ·
                      rfl

theorem cell23_5668100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_5668100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668100 prefixEnd_5668100 := by exact prefixLift 5668100
  have htrace : WordTrace (prefixWord ++ tailWord_5668100) baseStart_5668100 baseEnd_5668100 := by
    simpa [prefixWord, tailWord_5668100, baseEnd_5668100] using wordTrace_append hprefix tailTrace_5668100
  have hstable : (prefixWord ++ tailWord_5668100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668100).length < 2 ^ (prefixWord ++ tailWord_5668100).sum := by decide
  have hdescent : baseEnd_5668100 < baseStart_5668100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668141 : List Nat := [1, 5, 3, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_5668141 : Nat := 118140960795 + 5668141 * 2 ^ 59
def prefixEnd_5668141 : Nat := 4983230072969 + 3 ^ 40 * 5668141 * 2
def baseEnd_5668141 : Nat := 2910480750456213105970201

theorem tailTrace_5668141 : CollatzResearch.WordTrace tailWord_5668141 prefixEnd_5668141 2910480750456213105970201 := by
  unfold tailWord_5668141
  simp only [CollatzResearch.WordTrace]
  refine ⟨206734086158300673258196277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137822724105533782172130851 206734086158300673258196277)
  ·
    refine ⟨19381320577340688117955901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206734086158300673258196277 19381320577340688117955901)
    ·
      refine ⟨7267995216502758044233463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19381320577340688117955901 7267995216502758044233463)
      ·
        refine ⟨10901992824754137066350195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7267995216502758044233463 10901992824754137066350195)
        ·
          refine ⟨16352989237131205599525293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10901992824754137066350195 16352989237131205599525293)
          ·
            refine ⟨6132370963924202099821985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16352989237131205599525293 6132370963924202099821985)
            ·
              refine ⟨4599278222943151574866489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6132370963924202099821985 4599278222943151574866489)
              ·
                refine ⟨3449458667207363681149867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4599278222943151574866489 3449458667207363681149867)
                ·
                  refine ⟨5174188000811045521724801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3449458667207363681149867 5174188000811045521724801)
                  ·
                    refine ⟨3880641000608284141293601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5174188000811045521724801 3880641000608284141293601)
                    ·
                      refine ⟨2910480750456213105970201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3880641000608284141293601 2910480750456213105970201)
                      ·
                        rfl

theorem cell23_5668141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_5668141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668141 prefixEnd_5668141 := by exact prefixLift 5668141
  have htrace : WordTrace (prefixWord ++ tailWord_5668141) baseStart_5668141 baseEnd_5668141 := by
    simpa [prefixWord, tailWord_5668141, baseEnd_5668141] using wordTrace_append hprefix tailTrace_5668141
  have hstable : (prefixWord ++ tailWord_5668141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668141).length < 2 ^ (prefixWord ++ tailWord_5668141).sum := by decide
  have hdescent : baseEnd_5668141 < baseStart_5668141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668159 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 4]
def baseStart_5668159 : Nat := 118140960795 + 5668159 * 2 ^ 59
def prefixEnd_5668159 : Nat := 4983230072969 + 3 ^ 40 * 5668159 * 2
def baseEnd_5668159 : Nat := 2910489993107994035545117

theorem tailTrace_5668159 : CollatzResearch.WordTrace tailWord_5668159 prefixEnd_5668159 2910489993107994035545117 := by
  unfold tailWord_5668159
  simp only [CollatzResearch.WordTrace]
  refine ⟨206734742672235462332351531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137823161781490308221567687 206734742672235462332351531)
  ·
    refine ⟨310102114008353193498527297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206734742672235462332351531 310102114008353193498527297)
    ·
      refine ⟨232576585506264895123895473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310102114008353193498527297 232576585506264895123895473)
      ·
        refine ⟨174432439129698671342921605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232576585506264895123895473 174432439129698671342921605)
        ·
          refine ⟨32706082336818500876797801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174432439129698671342921605 32706082336818500876797801)
          ·
            refine ⟨24529561752613875657598351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32706082336818500876797801 24529561752613875657598351)
            ·
              refine ⟨36794342628920813486397527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24529561752613875657598351 36794342628920813486397527)
              ·
                refine ⟨55191513943381220229596291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36794342628920813486397527 55191513943381220229596291)
                ·
                  refine ⟨82787270915071830344394437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55191513943381220229596291 82787270915071830344394437)
                  ·
                    refine ⟨15522613296575968189573957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82787270915071830344394437 15522613296575968189573957)
                    ·
                      refine ⟨2910489993107994035545117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15522613296575968189573957 2910489993107994035545117)
                      ·
                        rfl

theorem cell23_5668159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_5668159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668159 prefixEnd_5668159 := by exact prefixLift 5668159
  have htrace : WordTrace (prefixWord ++ tailWord_5668159) baseStart_5668159 baseEnd_5668159 := by
    simpa [prefixWord, tailWord_5668159, baseEnd_5668159] using wordTrace_append hprefix tailTrace_5668159
  have hstable : (prefixWord ++ tailWord_5668159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668159).length < 2 ^ (prefixWord ++ tailWord_5668159).sum := by decide
  have hdescent : baseEnd_5668159 < baseStart_5668159 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668179 : List Nat := [1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 3]
def baseStart_5668179 : Nat := 118140960795 + 5668179 * 2 ^ 59
def prefixEnd_5668179 : Nat := 4983230072969 + 3 ^ 40 * 5668179 * 2
def baseEnd_5668179 : Nat := 2910500262721083957295025

theorem tailTrace_5668179 : CollatzResearch.WordTrace tailWord_5668179 prefixEnd_5668179 2910500262721083957295025 := by
  unfold tailWord_5668179
  simp only [CollatzResearch.WordTrace]
  refine ⟨206735472132163005748079591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137823648088108670498719727 206735472132163005748079591)
  ·
    refine ⟨310103208198244508622119387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206735472132163005748079591 310103208198244508622119387)
    ·
      refine ⟨465154812297366762933179081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310103208198244508622119387 465154812297366762933179081)
      ·
        refine ⟨348866109223025072199884311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465154812297366762933179081 348866109223025072199884311)
        ·
          refine ⟨523299163834537608299826467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348866109223025072199884311 523299163834537608299826467)
          ·
            refine ⟨784948745751806412449739701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523299163834537608299826467 784948745751806412449739701)
            ·
              refine ⟨73588944914231851167163097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 784948745751806412449739701 73588944914231851167163097)
              ·
                refine ⟨55191708685673888375372323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73588944914231851167163097 55191708685673888375372323)
                ·
                  refine ⟨82787563028510832563058485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55191708685673888375372323 82787563028510832563058485)
                  ·
                    refine ⟨7761334033922890552786733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82787563028510832563058485 7761334033922890552786733)
                    ·
                      refine ⟨2910500262721083957295025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7761334033922890552786733 2910500262721083957295025)
                      ·
                        rfl

theorem cell23_5668179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 3].length) (baseStart_5668179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668179 prefixEnd_5668179 := by exact prefixLift 5668179
  have htrace : WordTrace (prefixWord ++ tailWord_5668179) baseStart_5668179 baseEnd_5668179 := by
    simpa [prefixWord, tailWord_5668179, baseEnd_5668179] using wordTrace_append hprefix tailTrace_5668179
  have hstable : (prefixWord ++ tailWord_5668179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668179).length < 2 ^ (prefixWord ++ tailWord_5668179).sum := by decide
  have hdescent : baseEnd_5668179 < baseStart_5668179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668186 : List Nat := [3, 1, 1, 2, 1, 2, 3, 5, 5]
def baseStart_5668186 : Nat := 118140960795 + 5668186 * 2 ^ 59
def prefixEnd_5668186 : Nat := 4983230072969 + 3 ^ 40 * 5668186 * 2
def baseEnd_5668186 : Nat := 323389317453962825545277

theorem tailTrace_5668186 : CollatzResearch.WordTrace tailWord_5668186 prefixEnd_5668186 323389317453962825545277 := by
  unfold tailWord_5668186
  simp only [CollatzResearch.WordTrace]
  refine ⟨51683931860784411485896103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137823818295425097295722941 51683931860784411485896103)
  ·
    refine ⟨77525897791176617228844155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51683931860784411485896103 77525897791176617228844155)
    ·
      refine ⟨116288846686764925843266233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77525897791176617228844155 116288846686764925843266233)
      ·
        refine ⟨87216635015073694382449675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116288846686764925843266233 87216635015073694382449675)
        ·
          refine ⟨130824952522610541573674513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87216635015073694382449675 130824952522610541573674513)
          ·
            refine ⟨98118714391957906180255885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130824952522610541573674513 98118714391957906180255885)
            ·
              refine ⟨36794517896984214817595957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98118714391957906180255885 36794517896984214817595957)
              ·
                refine ⟨3449486052842270139149621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36794517896984214817595957 3449486052842270139149621)
                ·
                  refine ⟨323389317453962825545277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3449486052842270139149621 323389317453962825545277)
                  ·
                    rfl

theorem cell23_5668186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 5, 5].length) (baseStart_5668186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668186 prefixEnd_5668186 := by exact prefixLift 5668186
  have htrace : WordTrace (prefixWord ++ tailWord_5668186) baseStart_5668186 baseEnd_5668186 := by
    simpa [prefixWord, tailWord_5668186, baseEnd_5668186] using wordTrace_append hprefix tailTrace_5668186
  have hstable : (prefixWord ++ tailWord_5668186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668186).length < 2 ^ (prefixWord ++ tailWord_5668186).sum := by decide
  have hdescent : baseEnd_5668186 < baseStart_5668186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668196 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 2, 3, 3]
def baseStart_5668196 : Nat := 118140960795 + 5668196 * 2 ^ 59
def prefixEnd_5668196 : Nat := 4983230072969 + 3 ^ 40 * 5668196 * 2
def baseEnd_5668196 : Nat := 2910508991892210390782447

theorem tailTrace_5668196 : CollatzResearch.WordTrace tailWord_5668196 prefixEnd_5668196 2910508991892210390782447 := by
  unfold tailWord_5668196
  simp only [CollatzResearch.WordTrace]
  refine ⟨103368046086550708825724221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137824061448734278434298961 103368046086550708825724221)
  ·
    refine ⟨38763017282456515809646583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103368046086550708825724221 38763017282456515809646583)
    ·
      refine ⟨58144525923684773714469875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38763017282456515809646583 58144525923684773714469875)
      ·
        refine ⟨87216788885527160571704813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58144525923684773714469875 87216788885527160571704813)
        ·
          refine ⟨32706295832072685214389305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87216788885527160571704813 32706295832072685214389305)
          ·
            refine ⟨24529721874054513910791979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32706295832072685214389305 24529721874054513910791979)
            ·
              refine ⟨36794582811081770866187969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24529721874054513910791979 36794582811081770866187969)
              ·
                refine ⟨27595937108311328149640977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36794582811081770866187969 27595937108311328149640977)
                ·
                  refine ⟨20696952831233496112230733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27595937108311328149640977 20696952831233496112230733)
                  ·
                    refine ⟨7761357311712561042086525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20696952831233496112230733 7761357311712561042086525)
                    ·
                      refine ⟨2910508991892210390782447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7761357311712561042086525 2910508991892210390782447)
                      ·
                        rfl

theorem cell23_5668196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_5668196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668196 prefixEnd_5668196 := by exact prefixLift 5668196
  have htrace : WordTrace (prefixWord ++ tailWord_5668196) baseStart_5668196 baseEnd_5668196 := by
    simpa [prefixWord, tailWord_5668196, baseEnd_5668196] using wordTrace_append hprefix tailTrace_5668196
  have hstable : (prefixWord ++ tailWord_5668196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668196).length < 2 ^ (prefixWord ++ tailWord_5668196).sum := by decide
  have hdescent : baseEnd_5668196 < baseStart_5668196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668209 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 5]
def baseStart_5668209 : Nat := 118140960795 + 5668209 * 2 ^ 59
def prefixEnd_5668209 : Nat := 4983230072969 + 3 ^ 40 * 5668209 * 2
def baseEnd_5668209 : Nat := 2910515667140718839919887

theorem tailTrace_5668209 : CollatzResearch.WordTrace tailWord_5668209 prefixEnd_5668209 2910515667140718839919887 := by
  unfold tailWord_5668209
  simp only [CollatzResearch.WordTrace]
  refine ⟨206736566322054320871671681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137824377548036213914447787 206736566322054320871671681)
  ·
    refine ⟨155052424741540740653753761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206736566322054320871671681 155052424741540740653753761)
    ·
      refine ⟨116289318556155555490315321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155052424741540740653753761 116289318556155555490315321)
      ·
        refine ⟨87216988917116666617736491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116289318556155555490315321 87216988917116666617736491)
        ·
          refine ⟨130825483375674999926604737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87216988917116666617736491 130825483375674999926604737)
          ·
            refine ⟨98119112531756249944953553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130825483375674999926604737 98119112531756249944953553)
            ·
              refine ⟨73589334398817187458715165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98119112531756249944953553 73589334398817187458715165)
              ·
                refine ⟨27596000399556445297018187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73589334398817187458715165 27596000399556445297018187)
                ·
                  refine ⟨41394000599334667945527281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27596000399556445297018187 41394000599334667945527281)
                  ·
                    refine ⟨31045500449501000959145461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41394000599334667945527281 31045500449501000959145461)
                    ·
                      refine ⟨2910515667140718839919887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31045500449501000959145461 2910515667140718839919887)
                      ·
                        rfl

theorem cell23_5668209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_5668209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668209 prefixEnd_5668209 := by exact prefixLift 5668209
  have htrace : WordTrace (prefixWord ++ tailWord_5668209) baseStart_5668209 baseEnd_5668209 := by
    simpa [prefixWord, tailWord_5668209, baseEnd_5668209] using wordTrace_append hprefix tailTrace_5668209
  have hstable : (prefixWord ++ tailWord_5668209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668209).length < 2 ^ (prefixWord ++ tailWord_5668209).sum := by decide
  have hdescent : baseEnd_5668209 < baseStart_5668209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668219 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 4]
def baseStart_5668219 : Nat := 118140960795 + 5668219 * 2 ^ 59
def prefixEnd_5668219 : Nat := 4983230072969 + 3 ^ 40 * 5668219 * 2
def baseEnd_5668219 : Nat := 2910520801947263800794841

theorem tailTrace_5668219 : CollatzResearch.WordTrace tailWord_5668219 prefixEnd_5668219 2910520801947263800794841 := by
  unfold tailWord_5668219
  simp only [CollatzResearch.WordTrace]
  refine ⟨206736931052018092579535711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137824620701345395053023807 206736931052018092579535711)
  ·
    refine ⟨310105396578027138869303567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206736931052018092579535711 310105396578027138869303567)
    ·
      refine ⟨465158094867040708303955351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310105396578027138869303567 465158094867040708303955351)
      ·
        refine ⟨697737142300561062455933027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465158094867040708303955351 697737142300561062455933027)
        ·
          refine ⟨1046605713450841593683899541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697737142300561062455933027 1046605713450841593683899541)
          ·
            refine ⟨49059642818008199703932791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1046605713450841593683899541 49059642818008199703932791)
            ·
              refine ⟨73589464227012299555899187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49059642818008199703932791 73589464227012299555899187)
              ·
                refine ⟨110384196340518449333848781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73589464227012299555899187 110384196340518449333848781)
                ·
                  refine ⟨41394073627694418500193293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110384196340518449333848781 41394073627694418500193293)
                  ·
                    refine ⟨15522777610385406937572485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41394073627694418500193293 15522777610385406937572485)
                    ·
                      refine ⟨2910520801947263800794841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15522777610385406937572485 2910520801947263800794841)
                      ·
                        rfl

theorem cell23_5668219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 4].length) (baseStart_5668219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668219 prefixEnd_5668219 := by exact prefixLift 5668219
  have htrace : WordTrace (prefixWord ++ tailWord_5668219) baseStart_5668219 baseEnd_5668219 := by
    simpa [prefixWord, tailWord_5668219, baseEnd_5668219] using wordTrace_append hprefix tailTrace_5668219
  have hstable : (prefixWord ++ tailWord_5668219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668219).length < 2 ^ (prefixWord ++ tailWord_5668219).sum := by decide
  have hdescent : baseEnd_5668219 < baseStart_5668219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668236 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 2, 1, 4]
def baseStart_5668236 : Nat := 118140960795 + 5668236 * 2 ^ 59
def prefixEnd_5668236 : Nat := 4983230072969 + 3 ^ 40 * 5668236 * 2
def baseEnd_5668236 : Nat := 2910529531118390234282263

theorem tailTrace_5668236 : CollatzResearch.WordTrace tailWord_5668236 prefixEnd_5668236 2910529531118390234282263 := by
  unfold tailWord_5668236
  simp only [CollatzResearch.WordTrace]
  refine ⟨103368775546478252241452281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137825034061971002988603041 103368775546478252241452281)
  ·
    refine ⟨77526581659858689181089211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103368775546478252241452281 77526581659858689181089211)
    ·
      refine ⟨116289872489788033771633817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77526581659858689181089211 116289872489788033771633817)
      ·
        refine ⟨87217404367341025328725363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116289872489788033771633817 87217404367341025328725363)
        ·
          refine ⟨130826106551011537993088045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87217404367341025328725363 130826106551011537993088045)
          ·
            refine ⟨49059789956629326747408017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130826106551011537993088045 49059789956629326747408017)
            ·
              refine ⟨36794842467471995060556013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49059789956629326747408017 36794842467471995060556013)
              ·
                refine ⟨13798065925301998147708505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36794842467471995060556013 13798065925301998147708505)
                ·
                  refine ⟨10348549443976498610781379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13798065925301998147708505 10348549443976498610781379)
                  ·
                    refine ⟨15522824165964747916172069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10348549443976498610781379 15522824165964747916172069)
                    ·
                      refine ⟨2910529531118390234282263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15522824165964747916172069 2910529531118390234282263)
                      ·
                        rfl

theorem cell23_5668236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_5668236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668236 prefixEnd_5668236 := by exact prefixLift 5668236
  have htrace : WordTrace (prefixWord ++ tailWord_5668236) baseStart_5668236 baseEnd_5668236 := by
    simpa [prefixWord, tailWord_5668236, baseEnd_5668236] using wordTrace_append hprefix tailTrace_5668236
  have hstable : (prefixWord ++ tailWord_5668236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668236).length < 2 ^ (prefixWord ++ tailWord_5668236).sum := by decide
  have hdescent : baseEnd_5668236 < baseStart_5668236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668253 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_5668253 : Nat := 118140960795 + 5668253 * 2 ^ 59
def prefixEnd_5668253 : Nat := 4983230072969 + 3 ^ 40 * 5668253 * 2
def baseEnd_5668253 : Nat := 2910538260289516667769685

theorem tailTrace_5668253 : CollatzResearch.WordTrace tailWord_5668253 prefixEnd_5668253 2910538260289516667769685 := by
  unfold tailWord_5668253
  simp only [CollatzResearch.WordTrace]
  refine ⟨206738171133894916386273413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137825447422596610924182275 206738171133894916386273413)
  ·
    refine ⟨38763407087605296822426265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206738171133894916386273413 38763407087605296822426265)
    ·
      refine ⟨29072555315703972616819699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38763407087605296822426265 29072555315703972616819699)
      ·
        refine ⟨43608832973555958925229549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29072555315703972616819699 43608832973555958925229549)
        ·
          refine ⟨16353312365083484596961081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43608832973555958925229549 16353312365083484596961081)
          ·
            refine ⟨12264984273812613447720811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16353312365083484596961081 12264984273812613447720811)
            ·
              refine ⟨18397476410718920171581217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12264984273812613447720811 18397476410718920171581217)
              ·
                refine ⟨13798107308039190128685913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18397476410718920171581217 13798107308039190128685913)
                ·
                  refine ⟨10348580481029392596514435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13798107308039190128685913 10348580481029392596514435)
                  ·
                    refine ⟨15522870721544088894771653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10348580481029392596514435 15522870721544088894771653)
                    ·
                      refine ⟨2910538260289516667769685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15522870721544088894771653 2910538260289516667769685)
                      ·
                        rfl

theorem cell23_5668253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_5668253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668253 prefixEnd_5668253 := by exact prefixLift 5668253
  have htrace : WordTrace (prefixWord ++ tailWord_5668253) baseStart_5668253 baseEnd_5668253 := by
    simpa [prefixWord, tailWord_5668253, baseEnd_5668253] using wordTrace_append hprefix tailTrace_5668253
  have hstable : (prefixWord ++ tailWord_5668253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668253).length < 2 ^ (prefixWord ++ tailWord_5668253).sum := by decide
  have hdescent : baseEnd_5668253 < baseStart_5668253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668259 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 8]
def baseStart_5668259 : Nat := 118140960795 + 5668259 * 2 ^ 59
def prefixEnd_5668259 : Nat := 4983230072969 + 3 ^ 40 * 5668259 * 2
def baseEnd_5668259 : Nat := 323393482352604849366073

theorem tailTrace_5668259 : CollatzResearch.WordTrace tailWord_5668259 prefixEnd_5668259 323393482352604849366073 := by
  unfold tailWord_5668259
  simp only [CollatzResearch.WordTrace]
  refine ⟨206738389971873179410991831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137825593314582119607327887 206738389971873179410991831)
  ·
    refine ⟨310107584957809769116487747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206738389971873179410991831 310107584957809769116487747)
    ·
      refine ⟨465161377436714653674731621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310107584957809769116487747 465161377436714653674731621)
      ·
        refine ⟨87217758269383997564012179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 465161377436714653674731621 87217758269383997564012179)
        ·
          refine ⟨130826637404075996346018269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87217758269383997564012179 130826637404075996346018269)
          ·
            refine ⟨49059989026528498629756851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130826637404075996346018269 49059989026528498629756851)
            ·
              refine ⟨73589983539792747944635277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49059989026528498629756851 73589983539792747944635277)
              ·
                refine ⟨27596243827422280479238229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73589983539792747944635277 27596243827422280479238229)
                ·
                  refine ⟨323393482352604849366073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27596243827422280479238229 323393482352604849366073)
                  ·
                    rfl

theorem cell23_5668259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 8].length) (baseStart_5668259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668259 prefixEnd_5668259 := by exact prefixLift 5668259
  have htrace : WordTrace (prefixWord ++ tailWord_5668259) baseStart_5668259 baseEnd_5668259 := by
    simpa [prefixWord, tailWord_5668259, baseEnd_5668259] using wordTrace_append hprefix tailTrace_5668259
  have hstable : (prefixWord ++ tailWord_5668259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668259).length < 2 ^ (prefixWord ++ tailWord_5668259).sum := by decide
  have hdescent : baseEnd_5668259 < baseStart_5668259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668310 : List Nat := [5, 2, 1, 1, 1, 3, 2, 2, 6]
def baseStart_5668310 : Nat := 118140960795 + 5668310 * 2 ^ 59
def prefixEnd_5668310 : Nat := 4983230072969 + 3 ^ 40 * 5668310 * 2
def baseEnd_5668310 : Nat := 323396392076313660528547

theorem tailTrace_5668310 : CollatzResearch.WordTrace tailWord_5668310 prefixEnd_5668310 323396392076313660528547 := by
  unfold tailWord_5668310
  simp only [CollatzResearch.WordTrace]
  refine ⟨12921265630918025945068649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137826833396458943414065589 12921265630918025945068649)
  ·
    refine ⟨9690949223188519458801487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12921265630918025945068649 9690949223188519458801487)
    ·
      refine ⟨14536423834782779188202231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9690949223188519458801487 14536423834782779188202231)
      ·
        refine ⟨21804635752174168782303347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14536423834782779188202231 21804635752174168782303347)
        ·
          refine ⟨32706953628261253173455021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21804635752174168782303347 32706953628261253173455021)
          ·
            refine ⟨12265107610597969940045633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32706953628261253173455021 12265107610597969940045633)
            ·
              refine ⟨9198830707948477455034225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12265107610597969940045633 9198830707948477455034225)
              ·
                refine ⟨6899123030961358091275669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9198830707948477455034225 6899123030961358091275669)
                ·
                  refine ⟨323396392076313660528547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6899123030961358091275669 323396392076313660528547)
                  ·
                    rfl

theorem cell23_5668310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_5668310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668310 prefixEnd_5668310 := by exact prefixLift 5668310
  have htrace : WordTrace (prefixWord ++ tailWord_5668310) baseStart_5668310 baseEnd_5668310 := by
    simpa [prefixWord, tailWord_5668310, baseEnd_5668310] using wordTrace_append hprefix tailTrace_5668310
  have hstable : (prefixWord ++ tailWord_5668310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668310).length < 2 ^ (prefixWord ++ tailWord_5668310).sum := by decide
  have hdescent : baseEnd_5668310 < baseStart_5668310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668336 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 1, 6]
def baseStart_5668336 : Nat := 118140960795 + 5668336 * 2 ^ 59
def prefixEnd_5668336 : Nat := 4983230072969 + 3 ^ 40 * 5668336 * 2
def baseEnd_5668336 : Nat := 970193626394613281010601

theorem tailTrace_5668336 : CollatzResearch.WordTrace tailWord_5668336 prefixEnd_5668336 970193626394613281010601 := by
  unfold tailWord_5668336
  simp only [CollatzResearch.WordTrace]
  refine ⟨103370599196297110780772431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137827465595062814374363241 103370599196297110780772431)
  ·
    refine ⟨155055898794445666171158647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103370599196297110780772431 155055898794445666171158647)
    ·
      refine ⟨232583848191668499256737971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155055898794445666171158647 232583848191668499256737971)
      ·
        refine ⟨348875772287502748885106957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232583848191668499256737971 348875772287502748885106957)
        ·
          refine ⟨130828414607813530831915109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348875772287502748885106957 130828414607813530831915109)
          ·
            refine ⟨24530327738965037030984083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130828414607813530831915109 24530327738965037030984083)
            ·
              refine ⟨36795491608447555546476125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24530327738965037030984083 36795491608447555546476125)
              ·
                refine ⟨13798309353167833329928547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36795491608447555546476125 13798309353167833329928547)
                ·
                  refine ⟨20697464029751749994892821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13798309353167833329928547 20697464029751749994892821)
                  ·
                    refine ⟨970193626394613281010601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20697464029751749994892821 970193626394613281010601)
                    ·
                      rfl

theorem cell23_5668336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 1, 6].length) (baseStart_5668336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668336 prefixEnd_5668336 := by exact prefixLift 5668336
  have htrace : WordTrace (prefixWord ++ tailWord_5668336) baseStart_5668336 baseEnd_5668336 := by
    simpa [prefixWord, tailWord_5668336, baseEnd_5668336] using wordTrace_append hprefix tailTrace_5668336
  have hstable : (prefixWord ++ tailWord_5668336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668336).length < 2 ^ (prefixWord ++ tailWord_5668336).sum := by decide
  have hdescent : baseEnd_5668336 < baseStart_5668336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668354 : List Nat := [3, 4, 1, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_5668354 : Nat := 118140960795 + 5668354 * 2 ^ 59
def prefixEnd_5668354 : Nat := 4983230072969 + 3 ^ 40 * 5668354 * 2
def baseEnd_5668354 : Nat := 2910590121835620772606721

theorem tailTrace_5668354 : CollatzResearch.WordTrace tailWord_5668354 prefixEnd_5668354 2910590121835620772606721 := by
  unfold tailWord_5668354
  simp only [CollatzResearch.WordTrace]
  refine ⟨51685463726632252658925029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137827903271019340423800077 51685463726632252658925029)
  ·
    refine ⟨9691024448743547373548443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51685463726632252658925029 9691024448743547373548443)
    ·
      refine ⟨14536536673115321060322665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9691024448743547373548443 14536536673115321060322665)
      ·
        refine ⟨10902402504836490795241999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14536536673115321060322665 10902402504836490795241999)
        ·
          refine ⟨16353603757254736192862999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10902402504836490795241999 16353603757254736192862999)
          ·
            refine ⟨24530405635882104289294499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16353603757254736192862999 24530405635882104289294499)
            ·
              refine ⟨36795608453823156433941749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24530405635882104289294499 36795608453823156433941749)
              ·
                refine ⟨3449588292545920915682039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36795608453823156433941749 3449588292545920915682039)
                ·
                  refine ⟨5174382438818881373523059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3449588292545920915682039 5174382438818881373523059)
                  ·
                    refine ⟨7761573658228322060284589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5174382438818881373523059 7761573658228322060284589)
                    ·
                      refine ⟨2910590121835620772606721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7761573658228322060284589 2910590121835620772606721)
                      ·
                        rfl

theorem cell23_5668354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_5668354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668354 prefixEnd_5668354 := by exact prefixLift 5668354
  have htrace : WordTrace (prefixWord ++ tailWord_5668354) baseStart_5668354 baseEnd_5668354 := by
    simpa [prefixWord, tailWord_5668354, baseEnd_5668354] using wordTrace_append hprefix tailTrace_5668354
  have hstable : (prefixWord ++ tailWord_5668354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668354).length < 2 ^ (prefixWord ++ tailWord_5668354).sum := by decide
  have hdescent : baseEnd_5668354 < baseStart_5668354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668360 : List Nat := [2, 1, 3, 2, 1, 1, 6, 1, 1, 1, 4]
def baseStart_5668360 : Nat := 118140960795 + 5668360 * 2 ^ 59
def prefixEnd_5668360 : Nat := 4983230072969 + 3 ^ 40 * 5668360 * 2
def baseEnd_5668360 : Nat := 2910593202719547749131693

theorem tailTrace_5668360 : CollatzResearch.WordTrace tailWord_5668360 prefixEnd_5668360 2910593202719547749131693 := by
  unfold tailWord_5668360
  simp only [CollatzResearch.WordTrace]
  refine ⟨103371036872253636830209267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137828049163004849106945689 103371036872253636830209267)
  ·
    refine ⟨155056555308380455245313901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103371036872253636830209267 155056555308380455245313901)
    ·
      refine ⟨58146208240642670716992713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155056555308380455245313901 58146208240642670716992713)
      ·
        refine ⟨43609656180482003037744535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58146208240642670716992713 43609656180482003037744535)
        ·
          refine ⟨65414484270723004556616803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43609656180482003037744535 65414484270723004556616803)
          ·
            refine ⟨98121726406084506834925205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65414484270723004556616803 98121726406084506834925205)
            ·
              refine ⟨4599455925285211257887119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98121726406084506834925205 4599455925285211257887119)
              ·
                refine ⟨6899183887927816886830679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4599455925285211257887119 6899183887927816886830679)
                ·
                  refine ⟨10348775831891725330246019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6899183887927816886830679 10348775831891725330246019)
                  ·
                    refine ⟨15523163747837587995369029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10348775831891725330246019 15523163747837587995369029)
                    ·
                      refine ⟨2910593202719547749131693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15523163747837587995369029 2910593202719547749131693)
                      ·
                        rfl

theorem cell23_5668360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_5668360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668360 prefixEnd_5668360 := by exact prefixLift 5668360
  have htrace : WordTrace (prefixWord ++ tailWord_5668360) baseStart_5668360 baseEnd_5668360 := by
    simpa [prefixWord, tailWord_5668360, baseEnd_5668360] using wordTrace_append hprefix tailTrace_5668360
  have hstable : (prefixWord ++ tailWord_5668360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668360).length < 2 ^ (prefixWord ++ tailWord_5668360).sum := by decide
  have hdescent : baseEnd_5668360 < baseStart_5668360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668387 : List Nat := [1, 1, 1, 4, 5, 1, 3, 1, 2, 4]
def baseStart_5668387 : Nat := 118140960795 + 5668387 * 2 ^ 59
def prefixEnd_5668387 : Nat := 4983230072969 + 3 ^ 40 * 5668387 * 2
def baseEnd_5668387 : Nat := 970202355565739714498023

theorem tailTrace_5668387 : CollatzResearch.WordTrace tailWord_5668387 prefixEnd_5668387 970202355565739714498023 := by
  unfold tailWord_5668387
  simp only [CollatzResearch.WordTrace]
  refine ⟨206743058515409457271651415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137828705676939638181100943 206743058515409457271651415)
  ·
    refine ⟨310114587773114185907477123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206743058515409457271651415 310114587773114185907477123)
    ·
      refine ⟨465171881659671278861215685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310114587773114185907477123 465171881659671278861215685)
      ·
        refine ⟨87219727811188364786477941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 465171881659671278861215685 87219727811188364786477941)
        ·
          refine ⟨8176849482298909198732307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87219727811188364786477941 8176849482298909198732307)
          ·
            refine ⟨12265274223448363798098461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8176849482298909198732307 12265274223448363798098461)
            ·
              refine ⟨4599477833793136424286923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12265274223448363798098461 4599477833793136424286923)
              ·
                refine ⟨6899216750689704636430385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4599477833793136424286923 6899216750689704636430385)
                ·
                  refine ⟨5174412563017278477322789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6899216750689704636430385 5174412563017278477322789)
                  ·
                    refine ⟨970202355565739714498023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5174412563017278477322789 970202355565739714498023)
                    ·
                      rfl

theorem cell23_5668387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 2, 4].length) (baseStart_5668387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668387 prefixEnd_5668387 := by exact prefixLift 5668387
  have htrace : WordTrace (prefixWord ++ tailWord_5668387) baseStart_5668387 baseEnd_5668387 := by
    simpa [prefixWord, tailWord_5668387, baseEnd_5668387] using wordTrace_append hprefix tailTrace_5668387
  have hstable : (prefixWord ++ tailWord_5668387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668387).length < 2 ^ (prefixWord ++ tailWord_5668387).sum := by decide
  have hdescent : baseEnd_5668387 < baseStart_5668387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668416 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 4]
def baseStart_5668416 : Nat := 118140960795 + 5668416 * 2 ^ 59
def prefixEnd_5668416 : Nat := 4983230072969 + 3 ^ 40 * 5668416 * 2
def baseEnd_5668416 : Nat := 2910621957636199530031435

theorem tailTrace_5668416 : CollatzResearch.WordTrace tailWord_5668416 prefixEnd_5668416 2910621957636199530031435 := by
  unfold tailWord_5668416
  simp only [CollatzResearch.WordTrace]
  refine ⟨103372058116152197612228551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137829410821536263482971401 103372058116152197612228551)
  ·
    refine ⟨155058087174228296418342827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103372058116152197612228551 155058087174228296418342827)
    ·
      refine ⟨232587130761342444627514241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155058087174228296418342827 232587130761342444627514241)
      ·
        refine ⟨174440348071006833470635681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232587130761342444627514241 174440348071006833470635681)
        ·
          refine ⟨130830261053255125102976761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174440348071006833470635681 130830261053255125102976761)
          ·
            refine ⟨98122695789941343827232571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130830261053255125102976761 98122695789941343827232571)
            ·
              refine ⟨147184043684912015740848857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98122695789941343827232571 147184043684912015740848857)
              ·
                refine ⟨110388032763684011805636643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147184043684912015740848857 110388032763684011805636643)
                ·
                  refine ⟨165582049145526017708454965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110388032763684011805636643 165582049145526017708454965)
                  ·
                    refine ⟨15523317107393064160167653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 165582049145526017708454965 15523317107393064160167653)
                    ·
                      refine ⟨2910621957636199530031435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15523317107393064160167653 2910621957636199530031435)
                      ·
                        rfl

theorem cell23_5668416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_5668416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668416 prefixEnd_5668416 := by exact prefixLift 5668416
  have htrace : WordTrace (prefixWord ++ tailWord_5668416) baseStart_5668416 baseEnd_5668416 := by
    simpa [prefixWord, tailWord_5668416, baseEnd_5668416] using wordTrace_append hprefix tailTrace_5668416
  have hstable : (prefixWord ++ tailWord_5668416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668416).length < 2 ^ (prefixWord ++ tailWord_5668416).sum := by decide
  have hdescent : baseEnd_5668416 < baseStart_5668416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668438 : List Nat := [5, 2, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_5668438 : Nat := 118140960795 + 5668438 * 2 ^ 59
def prefixEnd_5668438 : Nat := 4983230072969 + 3 ^ 40 * 5668438 * 2
def baseEnd_5668438 : Nat := 970211084736866147985445

theorem tailTrace_5668438 : CollatzResearch.WordTrace tailWord_5668438 prefixEnd_5668438 970211084736866147985445 := by
  unfold tailWord_5668438
  simp only [CollatzResearch.WordTrace]
  refine ⟨12921557414889043311359873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137829945758816461987838645 12921557414889043311359873)
  ·
    refine ⟨9691168061166782483519905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12921557414889043311359873 9691168061166782483519905)
    ·
      refine ⟨7268376045875086862639929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9691168061166782483519905 7268376045875086862639929)
      ·
        refine ⟨5451282034406315146979947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7268376045875086862639929 5451282034406315146979947)
        ·
          refine ⟨8176923051609472720469921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5451282034406315146979947 8176923051609472720469921)
          ·
            refine ⟨6132692288707104540352441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8176923051609472720469921 6132692288707104540352441)
            ·
              refine ⟨4599519216530328405264331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6132692288707104540352441 4599519216530328405264331)
              ·
                refine ⟨6899278824795492607896497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4599519216530328405264331 6899278824795492607896497)
                ·
                  refine ⟨5174459118596619455922373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6899278824795492607896497 5174459118596619455922373)
                  ·
                    refine ⟨970211084736866147985445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5174459118596619455922373 970211084736866147985445)
                    ·
                      rfl

theorem cell23_5668438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_5668438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668438 prefixEnd_5668438 := by exact prefixLift 5668438
  have htrace : WordTrace (prefixWord ++ tailWord_5668438) baseStart_5668438 baseEnd_5668438 := by
    simpa [prefixWord, tailWord_5668438, baseEnd_5668438] using wordTrace_append hprefix tailTrace_5668438
  have hstable : (prefixWord ++ tailWord_5668438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668438).length < 2 ^ (prefixWord ++ tailWord_5668438).sum := by decide
  have hdescent : baseEnd_5668438 < baseStart_5668438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668444 : List Nat := [2, 2, 4, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_5668444 : Nat := 118140960795 + 5668444 * 2 ^ 59
def prefixEnd_5668444 : Nat := 4983230072969 + 3 ^ 40 * 5668444 * 2
def baseEnd_5668444 : Nat := 2910636335094525420481307

theorem tailTrace_5668444 : CollatzResearch.WordTrace tailWord_5668444 prefixEnd_5668444 2910636335094525420481307 := by
  unfold tailWord_5668444
  simp only [CollatzResearch.WordTrace]
  refine ⟨103372568738101478003238193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137830091650801970670984257 103372568738101478003238193)
  ·
    refine ⟨77529426553576108502428645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103372568738101478003238193 77529426553576108502428645)
    ·
      refine ⟨14536767478795520344205371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77529426553576108502428645 14536767478795520344205371)
      ·
        refine ⟨21805151218193280516308057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14536767478795520344205371 21805151218193280516308057)
        ·
          refine ⟨16353863413644960387231043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21805151218193280516308057 16353863413644960387231043)
          ·
            refine ⟨24530795120467440580846565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16353863413644960387231043 24530795120467440580846565)
            ·
              refine ⟨4599524085087645108908731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24530795120467440580846565 4599524085087645108908731)
              ·
                refine ⟨6899286127631467663363097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4599524085087645108908731 6899286127631467663363097)
                ·
                  refine ⟨5174464595723600747522323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6899286127631467663363097 5174464595723600747522323)
                  ·
                    refine ⟨7761696893585401121283485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5174464595723600747522323 7761696893585401121283485)
                    ·
                      refine ⟨2910636335094525420481307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7761696893585401121283485 2910636335094525420481307)
                      ·
                        rfl

theorem cell23_5668444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_5668444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668444 prefixEnd_5668444 := by exact prefixLift 5668444
  have htrace : WordTrace (prefixWord ++ tailWord_5668444) baseStart_5668444 baseEnd_5668444 := by
    simpa [prefixWord, tailWord_5668444, baseEnd_5668444] using wordTrace_append hprefix tailTrace_5668444
  have hstable : (prefixWord ++ tailWord_5668444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668444).length < 2 ^ (prefixWord ++ tailWord_5668444).sum := by decide
  have hdescent : baseEnd_5668444 < baseStart_5668444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668453 : List Nat := [1, 3, 1, 3, 3, 1, 1, 2, 2, 1, 5]
def baseStart_5668453 : Nat := 118140960795 + 5668453 * 2 ^ 59
def prefixEnd_5668453 : Nat := 4983230072969 + 3 ^ 40 * 5668453 * 2
def baseEnd_5668453 : Nat := 2910640956420415885268765

theorem tailTrace_5668453 : CollatzResearch.WordTrace tailWord_5668453 prefixEnd_5668453 2910640956420415885268765 := by
  unfold tailWord_5668453
  simp only [CollatzResearch.WordTrace]
  refine ⟨206745465733170350543554013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137830310488780233695702675 206745465733170350543554013)
  ·
    refine ⟨77529549649938881453832755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206745465733170350543554013 77529549649938881453832755)
    ·
      refine ⟨116294324474908322180749133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77529549649938881453832755 116294324474908322180749133)
      ·
        refine ⟨43610371678090620817780925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116294324474908322180749133 43610371678090620817780925)
        ·
          refine ⟨16353889379283982806667847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43610371678090620817780925 16353889379283982806667847)
          ·
            refine ⟨24530834068925974210001771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16353889379283982806667847 24530834068925974210001771)
            ·
              refine ⟨36796251103388961315002657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24530834068925974210001771 36796251103388961315002657)
              ·
                refine ⟨27597188327541720986251993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36796251103388961315002657 27597188327541720986251993)
                ·
                  refine ⟨20697891245656290739688995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27597188327541720986251993 20697891245656290739688995)
                  ·
                    refine ⟨31046836868484436109533493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20697891245656290739688995 31046836868484436109533493)
                    ·
                      refine ⟨2910640956420415885268765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31046836868484436109533493 2910640956420415885268765)
                      ·
                        rfl

theorem cell23_5668453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_5668453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668453 prefixEnd_5668453 := by exact prefixLift 5668453
  have htrace : WordTrace (prefixWord ++ tailWord_5668453) baseStart_5668453 baseEnd_5668453 := by
    simpa [prefixWord, tailWord_5668453, baseEnd_5668453] using wordTrace_append hprefix tailTrace_5668453
  have hstable : (prefixWord ++ tailWord_5668453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668453).length < 2 ^ (prefixWord ++ tailWord_5668453).sum := by decide
  have hdescent : baseEnd_5668453 < baseStart_5668453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668470 : List Nat := [5, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5]
def baseStart_5668470 : Nat := 118140960795 + 5668470 * 2 ^ 59
def prefixEnd_5668470 : Nat := 4983230072969 + 3 ^ 40 * 5668470 * 2
def baseEnd_5668470 : Nat := 2910649685591542318756187

theorem tailTrace_5668470 : CollatzResearch.WordTrace tailWord_5668470 prefixEnd_5668470 2910649685591542318756187 := by
  unfold tailWord_5668470
  simp only [CollatzResearch.WordTrace]
  refine ⟨12921630360881797652932679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137830723849405841631281909 12921630360881797652932679)
  ·
    refine ⟨19382445541322696479399019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12921630360881797652932679 19382445541322696479399019)
    ·
      refine ⟨29073668311984044719098529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19382445541322696479399019 29073668311984044719098529)
      ·
        refine ⟨21805251233988033539323897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29073668311984044719098529 21805251233988033539323897)
        ·
          refine ⟨16353938425491025154492923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21805251233988033539323897 16353938425491025154492923)
          ·
            refine ⟨24530907638236537731739385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16353938425491025154492923 24530907638236537731739385)
            ·
              refine ⟨18398180728677403298804539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24530907638236537731739385 18398180728677403298804539)
              ·
                refine ⟨27597271093016104948206809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18398180728677403298804539 27597271093016104948206809)
                ·
                  refine ⟨20697953319762078711155107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27597271093016104948206809 20697953319762078711155107)
                  ·
                    refine ⟨31046929979643118066732661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20697953319762078711155107 31046929979643118066732661)
                    ·
                      refine ⟨2910649685591542318756187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31046929979643118066732661 2910649685591542318756187)
                      ·
                        rfl

theorem cell23_5668470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_5668470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668470 prefixEnd_5668470 := by exact prefixLift 5668470
  have htrace : WordTrace (prefixWord ++ tailWord_5668470) baseStart_5668470 baseEnd_5668470 := by
    simpa [prefixWord, tailWord_5668470, baseEnd_5668470] using wordTrace_append hprefix tailTrace_5668470
  have hstable : (prefixWord ++ tailWord_5668470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668470).length < 2 ^ (prefixWord ++ tailWord_5668470).sum := by decide
  have hdescent : baseEnd_5668470 < baseStart_5668470 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668483 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 3]
def baseStart_5668483 : Nat := 118140960795 + 5668483 * 2 ^ 59
def prefixEnd_5668483 : Nat := 4983230072969 + 3 ^ 40 * 5668483 * 2
def baseEnd_5668483 : Nat := 2910656360840050767893627

theorem tailTrace_5668483 : CollatzResearch.WordTrace tailWord_5668483 prefixEnd_5668483 2910656360840050767893627 := by
  unfold tailWord_5668483
  simp only [CollatzResearch.WordTrace]
  refine ⟨206746559923061665667146103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137831039948707777111430735 206746559923061665667146103)
  ·
    refine ⟨310119839884592498500719155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206746559923061665667146103 310119839884592498500719155)
    ·
      refine ⟨465179759826888747751078733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310119839884592498500719155 465179759826888747751078733)
      ·
        refine ⟨174442409935083280406654525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 465179759826888747751078733 174442409935083280406654525)
        ·
          refine ⟨65415903725656230152495447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174442409935083280406654525 65415903725656230152495447)
          ·
            refine ⟨98123855588484345228743171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65415903725656230152495447 98123855588484345228743171)
            ·
              refine ⟨147185783382726517843114757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98123855588484345228743171 147185783382726517843114757)
              ·
                refine ⟨27597334384261222095584017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147185783382726517843114757 27597334384261222095584017)
                ·
                  refine ⟨20698000788195916571688013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27597334384261222095584017 20698000788195916571688013)
                  ·
                    refine ⟨7761750295573468714383005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20698000788195916571688013 7761750295573468714383005)
                    ·
                      refine ⟨2910656360840050767893627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7761750295573468714383005 2910656360840050767893627)
                      ·
                        rfl

theorem cell23_5668483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_5668483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668483 prefixEnd_5668483 := by exact prefixLift 5668483
  have htrace : WordTrace (prefixWord ++ tailWord_5668483) baseStart_5668483 baseEnd_5668483 := by
    simpa [prefixWord, tailWord_5668483, baseEnd_5668483] using wordTrace_append hprefix tailTrace_5668483
  have hstable : (prefixWord ++ tailWord_5668483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668483).length < 2 ^ (prefixWord ++ tailWord_5668483).sum := by decide
  have hdescent : baseEnd_5668483 < baseStart_5668483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668557 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_5668557 : Nat := 118140960795 + 5668557 * 2 ^ 59
def prefixEnd_5668557 : Nat := 4983230072969 + 3 ^ 40 * 5668557 * 2
def baseEnd_5668557 : Nat := 2910694358408483478368287

theorem tailTrace_5668557 : CollatzResearch.WordTrace tailWord_5668557 prefixEnd_5668557 2910694358408483478368287 := by
  unfold tailWord_5668557
  simp only [CollatzResearch.WordTrace]
  refine ⟨206749258924793576305339925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137832839283195717536893283 206749258924793576305339925)
  ·
    refine ⟨9691371512099698889312809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 206749258924793576305339925 9691371512099698889312809)
    ·
      refine ⟨7268528634074774166984607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9691371512099698889312809 7268528634074774166984607)
      ·
        refine ⟨10902792951112161250476911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7268528634074774166984607 10902792951112161250476911)
        ·
          refine ⟨16354189426668241875715367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10902792951112161250476911 16354189426668241875715367)
          ·
            refine ⟨24531284140002362813573051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16354189426668241875715367 24531284140002362813573051)
            ·
              refine ⟨36796926210003544220359577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24531284140002362813573051 36796926210003544220359577)
              ·
                refine ⟨27597694657502658165269683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36796926210003544220359577 27597694657502658165269683)
                ·
                  refine ⟨41396541986253987247904525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27597694657502658165269683 41396541986253987247904525)
                  ·
                    refine ⟨15523703244845245217964197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41396541986253987247904525 15523703244845245217964197)
                    ·
                      refine ⟨2910694358408483478368287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15523703244845245217964197 2910694358408483478368287)
                      ·
                        rfl

theorem cell23_5668557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_5668557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668557 prefixEnd_5668557 := by exact prefixLift 5668557
  have htrace : WordTrace (prefixWord ++ tailWord_5668557) baseStart_5668557 baseEnd_5668557 := by
    simpa [prefixWord, tailWord_5668557, baseEnd_5668557] using wordTrace_append hprefix tailTrace_5668557
  have hstable : (prefixWord ++ tailWord_5668557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668557).length < 2 ^ (prefixWord ++ tailWord_5668557).sum := by decide
  have hdescent : baseEnd_5668557 < baseStart_5668557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668584 : List Nat := [2, 1, 4, 1, 3, 1, 3, 3, 1, 4]
def baseStart_5668584 : Nat := 118140960795 + 5668584 * 2 ^ 59
def prefixEnd_5668584 : Nat := 4983230072969 + 3 ^ 40 * 5668584 * 2
def baseEnd_5668584 : Nat := 970236074128718290910221

theorem tailTrace_5668584 : CollatzResearch.WordTrace tailWord_5668584 prefixEnd_5668584 970236074128718290910221 := by
  unfold tailWord_5668584
  simp only [CollatzResearch.WordTrace]
  refine ⟨103375121847847879958286403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137833495797130506611048537 103375121847847879958286403)
  ·
    refine ⟨155062682771771819937429605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103375121847847879958286403 155062682771771819937429605)
    ·
      refine ⟨29074253019707216238268051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155062682771771819937429605 29074253019707216238268051)
      ·
        refine ⟨43611379529560824357402077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29074253019707216238268051 43611379529560824357402077)
        ·
          refine ⟨16354267323585309134025779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43611379529560824357402077 16354267323585309134025779)
          ·
            refine ⟨24531400985377963701038669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16354267323585309134025779 24531400985377963701038669)
            ·
              refine ⟨9199275369516736387889501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24531400985377963701038669 9199275369516736387889501)
              ·
                refine ⟨3449728263568776145458563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9199275369516736387889501 3449728263568776145458563)
                ·
                  refine ⟨5174592395353164218187845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3449728263568776145458563 5174592395353164218187845)
                  ·
                    refine ⟨970236074128718290910221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5174592395353164218187845 970236074128718290910221)
                    ·
                      rfl

theorem cell23_5668584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_5668584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668584 prefixEnd_5668584 := by exact prefixLift 5668584
  have htrace : WordTrace (prefixWord ++ tailWord_5668584) baseStart_5668584 baseEnd_5668584 := by
    simpa [prefixWord, tailWord_5668584, baseEnd_5668584] using wordTrace_append hprefix tailTrace_5668584
  have hstable : (prefixWord ++ tailWord_5668584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668584).length < 2 ^ (prefixWord ++ tailWord_5668584).sum := by decide
  have hdescent : baseEnd_5668584 < baseStart_5668584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668600 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 3, 5, 2]
def baseStart_5668600 : Nat := 118140960795 + 5668600 * 2 ^ 59
def prefixEnd_5668600 : Nat := 4983230072969 + 3 ^ 40 * 5668600 * 2
def baseEnd_5668600 : Nat := 2910716438076626810130589

theorem tailTrace_5668600 : CollatzResearch.WordTrace tailWord_5668600 prefixEnd_5668600 2910716438076626810130589 := by
  unfold tailWord_5668600
  simp only [CollatzResearch.WordTrace]
  refine ⟨103375413631818897324577627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137833884842425196432770169 103375413631818897324577627)
  ·
    refine ⟨155063120447728345986866441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103375413631818897324577627 155063120447728345986866441)
    ·
      refine ⟨116297340335796259490149831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155063120447728345986866441 116297340335796259490149831)
      ·
        refine ⟨174446010503694389235224747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116297340335796259490149831 174446010503694389235224747)
        ·
          refine ⟨261669015755541583852837121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174446010503694389235224747 261669015755541583852837121)
          ·
            refine ⟨196251761816656187889627841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261669015755541583852837121 196251761816656187889627841)
            ·
              refine ⟨147188821362492140917220881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196251761816656187889627841 147188821362492140917220881)
              ·
                refine ⟨110391616021869105687915661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147188821362492140917220881 110391616021869105687915661)
                ·
                  refine ⟨41396856008200914632968373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110391616021869105687915661 41396856008200914632968373)
                  ·
                    refine ⟨3880955250768835746840785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41396856008200914632968373 3880955250768835746840785)
                    ·
                      refine ⟨2910716438076626810130589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3880955250768835746840785 2910716438076626810130589)
                      ·
                        rfl

theorem cell23_5668600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 3, 5, 2].length) (baseStart_5668600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668600 prefixEnd_5668600 := by exact prefixLift 5668600
  have htrace : WordTrace (prefixWord ++ tailWord_5668600) baseStart_5668600 baseEnd_5668600 := by
    simpa [prefixWord, tailWord_5668600, baseEnd_5668600] using wordTrace_append hprefix tailTrace_5668600
  have hstable : (prefixWord ++ tailWord_5668600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668600).length < 2 ^ (prefixWord ++ tailWord_5668600).sum := by decide
  have hdescent : baseEnd_5668600 < baseStart_5668600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668607 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 3, 1, 3]
def baseStart_5668607 : Nat := 118140960795 + 5668607 * 2 ^ 59
def prefixEnd_5668607 : Nat := 4983230072969 + 3 ^ 40 * 5668607 * 2
def baseEnd_5668607 : Nat := 2910720032441208282743057

theorem tailTrace_5668607 : CollatzResearch.WordTrace tailWord_5668607 prefixEnd_5668607 2910720032441208282743057 := by
  unfold tailWord_5668607
  simp only [CollatzResearch.WordTrace]
  refine ⟨206751082574612434844660075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137834055049741623229773383 206751082574612434844660075)
  ·
    refine ⟨310126623861918652266990113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206751082574612434844660075 310126623861918652266990113)
    ·
      refine ⟨232594967896438989200242585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310126623861918652266990113 232594967896438989200242585)
      ·
        refine ⟨174446225922329241900181939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232594967896438989200242585 174446225922329241900181939)
        ·
          refine ⟨261669338883493862850272909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174446225922329241900181939 261669338883493862850272909)
          ·
            refine ⟨98126002081310198568852341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261669338883493862850272909 98126002081310198568852341)
            ·
              refine ⟨9199312695122831115829907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98126002081310198568852341 9199312695122831115829907)
              ·
                refine ⟨13798969042684246673744861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9199312695122831115829907 13798969042684246673744861)
                ·
                  refine ⟨5174613391006592502654323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13798969042684246673744861 5174613391006592502654323)
                  ·
                    refine ⟨7761920086509888753981485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5174613391006592502654323 7761920086509888753981485)
                    ·
                      refine ⟨2910720032441208282743057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7761920086509888753981485 2910720032441208282743057)
                      ·
                        rfl

theorem cell23_5668607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 1, 3].length) (baseStart_5668607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668607 prefixEnd_5668607 := by exact prefixLift 5668607
  have htrace : WordTrace (prefixWord ++ tailWord_5668607) baseStart_5668607 baseEnd_5668607 := by
    simpa [prefixWord, tailWord_5668607, baseEnd_5668607] using wordTrace_append hprefix tailTrace_5668607
  have hstable : (prefixWord ++ tailWord_5668607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668607).length < 2 ^ (prefixWord ++ tailWord_5668607).sum := by decide
  have hdescent : baseEnd_5668607 < baseStart_5668607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668613 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 1, 7, 4]
def baseStart_5668613 : Nat := 118140960795 + 5668613 * 2 ^ 59
def prefixEnd_5668613 : Nat := 4983230072969 + 3 ^ 40 * 5668613 * 2
def baseEnd_5668613 : Nat := 2910723113325135259268029

theorem tailTrace_5668613 : CollatzResearch.WordTrace tailWord_5668613 prefixEnd_5668613 2910723113325135259268029 := by
  unfold tailWord_5668613
  simp only [CollatzResearch.WordTrace]
  refine ⟨206751301412590697869378493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137834200941727131912918995 206751301412590697869378493)
  ·
    refine ⟨77531738029721511701016935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206751301412590697869378493 77531738029721511701016935)
    ·
      refine ⟨116297607044582267551525403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77531738029721511701016935 116297607044582267551525403)
      ·
        refine ⟨174446410566873401327288105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116297607044582267551525403 174446410566873401327288105)
        ·
          refine ⟨130834807925155050995466079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174446410566873401327288105 130834807925155050995466079)
          ·
            refine ⟨196252211887732576493199119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130834807925155050995466079 196252211887732576493199119)
            ·
              refine ⟨294378317831598864739798679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196252211887732576493199119 294378317831598864739798679)
              ·
                refine ⟨441567476747398297109698019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294378317831598864739798679 441567476747398297109698019)
                ·
                  refine ⟨662351215121097445664547029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441567476747398297109698019 662351215121097445664547029)
                  ·
                    refine ⟨15523856604400721382762821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 662351215121097445664547029 15523856604400721382762821)
                    ·
                      refine ⟨2910723113325135259268029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15523856604400721382762821 2910723113325135259268029)
                      ·
                        rfl

theorem cell23_5668613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 7, 4].length) (baseStart_5668613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668613 prefixEnd_5668613 := by exact prefixLift 5668613
  have htrace : WordTrace (prefixWord ++ tailWord_5668613) baseStart_5668613 baseEnd_5668613 := by
    simpa [prefixWord, tailWord_5668613, baseEnd_5668613] using wordTrace_append hprefix tailTrace_5668613
  have hstable : (prefixWord ++ tailWord_5668613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668613).length < 2 ^ (prefixWord ++ tailWord_5668613).sum := by decide
  have hdescent : baseEnd_5668613 < baseStart_5668613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668628 : List Nat := [2, 4, 4, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_5668628 : Nat := 118140960795 + 5668628 * 2 ^ 59
def prefixEnd_5668628 : Nat := 4983230072969 + 3 ^ 40 * 5668628 * 2
def baseEnd_5668628 : Nat := 2910730815534952700580461

theorem tailTrace_5668628 : CollatzResearch.WordTrace tailWord_5668628 prefixEnd_5668628 2910730815534952700580461 := by
  unfold tailWord_5668628
  simp only [CollatzResearch.WordTrace]
  refine ⟨103375924253768177715587269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137834565671690903620783025 103375924253768177715587269)
  ·
    refine ⟨19382985797581533321672613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103375924253768177715587269 19382985797581533321672613)
    ·
      refine ⟨3634309837046537497813615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19382985797581533321672613 3634309837046537497813615)
      ·
        refine ⟨5451464755569806246720423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3634309837046537497813615 5451464755569806246720423)
        ·
          refine ⟨8177197133354709370080635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5451464755569806246720423 8177197133354709370080635)
          ·
            refine ⟨12265795700032064055120953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8177197133354709370080635 12265795700032064055120953)
            ·
              refine ⟨9199346775024048041340715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12265795700032064055120953 9199346775024048041340715)
              ·
                refine ⟨13799020162536072062011073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9199346775024048041340715 13799020162536072062011073)
                ·
                  refine ⟨10349265121902054046508305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13799020162536072062011073 10349265121902054046508305)
                  ·
                    refine ⟨7761948841426540534881229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10349265121902054046508305 7761948841426540534881229)
                    ·
                      refine ⟨2910730815534952700580461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7761948841426540534881229 2910730815534952700580461)
                      ·
                        rfl

theorem cell23_5668628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_5668628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668628 prefixEnd_5668628 := by exact prefixLift 5668628
  have htrace : WordTrace (prefixWord ++ tailWord_5668628) baseStart_5668628 baseEnd_5668628 := by
    simpa [prefixWord, tailWord_5668628, baseEnd_5668628] using wordTrace_append hprefix tailTrace_5668628
  have hstable : (prefixWord ++ tailWord_5668628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668628).length < 2 ^ (prefixWord ++ tailWord_5668628).sum := by decide
  have hdescent : baseEnd_5668628 < baseStart_5668628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668634 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2]
def baseStart_5668634 : Nat := 118140960795 + 5668634 * 2 ^ 59
def prefixEnd_5668634 : Nat := 4983230072969 + 3 ^ 40 * 5668634 * 2
def baseEnd_5668634 : Nat := 2910733896418879677105433

theorem tailTrace_5668634 : CollatzResearch.WordTrace tailWord_5668634 prefixEnd_5668634 2910733896418879677105433 := by
  unfold tailWord_5668634
  simp only [CollatzResearch.WordTrace]
  refine ⟨51688016836378654613973239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137834711563676412303928637 51688016836378654613973239)
  ·
    refine ⟨77532025254567981920959859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51688016836378654613973239 77532025254567981920959859)
    ·
      refine ⟨116298037881851972881439789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77532025254567981920959859 116298037881851972881439789)
      ·
        refine ⟨43611764205694489830539921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116298037881851972881439789 43611764205694489830539921)
        ·
          refine ⟨32708823154270867372904941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43611764205694489830539921 32708823154270867372904941)
          ·
            refine ⟨12265808682851575264839353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32708823154270867372904941 12265808682851575264839353)
            ·
              refine ⟨9199356512138681448629515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12265808682851575264839353 9199356512138681448629515)
              ·
                refine ⟨13799034768208022172944273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9199356512138681448629515 13799034768208022172944273)
                ·
                  refine ⟨10349276076156016629708205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13799034768208022172944273 10349276076156016629708205)
                  ·
                    refine ⟨3880978528558506236140577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10349276076156016629708205 3880978528558506236140577)
                    ·
                      refine ⟨2910733896418879677105433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3880978528558506236140577 2910733896418879677105433)
                      ·
                        rfl

theorem cell23_5668634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_5668634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668634 prefixEnd_5668634 := by exact prefixLift 5668634
  have htrace : WordTrace (prefixWord ++ tailWord_5668634) baseStart_5668634 baseEnd_5668634 := by
    simpa [prefixWord, tailWord_5668634, baseEnd_5668634] using wordTrace_append hprefix tailTrace_5668634
  have hstable : (prefixWord ++ tailWord_5668634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668634).length < 2 ^ (prefixWord ++ tailWord_5668634).sum := by decide
  have hdescent : baseEnd_5668634 < baseStart_5668634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668640 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 1, 6]
def baseStart_5668640 : Nat := 118140960795 + 5668640 * 2 ^ 59
def prefixEnd_5668640 : Nat := 4983230072969 + 3 ^ 40 * 5668640 * 2
def baseEnd_5668640 : Nat := 970245659100935551210135

theorem tailTrace_5668640 : CollatzResearch.WordTrace tailWord_5668640 prefixEnd_5668640 970245659100935551210135 := by
  unfold tailWord_5668640
  simp only [CollatzResearch.WordTrace]
  refine ⟨103376143091746440740305687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137834857455661920987074249 103376143091746440740305687)
  ·
    refine ⟨155064214637619661110458531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103376143091746440740305687 155064214637619661110458531)
    ·
      refine ⟨232596321956429491665687797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155064214637619661110458531 232596321956429491665687797)
      ·
        refine ⟨21805905183415264843658231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 232596321956429491665687797 21805905183415264843658231)
        ·
          refine ⟨32708857775122897265487347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21805905183415264843658231 32708857775122897265487347)
          ·
            refine ⟨49063286662684345898231021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32708857775122897265487347 49063286662684345898231021)
            ·
              refine ⟨18398732498506629711836633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49063286662684345898231021 18398732498506629711836633)
              ·
                refine ⟨13799049373879972283877475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18398732498506629711836633 13799049373879972283877475)
                ·
                  refine ⟨20698574060819958425816213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13799049373879972283877475 20698574060819958425816213)
                  ·
                    refine ⟨970245659100935551210135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20698574060819958425816213 970245659100935551210135)
                    ·
                      rfl

theorem cell23_5668640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 1, 6].length) (baseStart_5668640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668640 prefixEnd_5668640 := by exact prefixLift 5668640
  have htrace : WordTrace (prefixWord ++ tailWord_5668640) baseStart_5668640 baseEnd_5668640 := by
    simpa [prefixWord, tailWord_5668640, baseEnd_5668640] using wordTrace_append hprefix tailTrace_5668640
  have hstable : (prefixWord ++ tailWord_5668640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668640).length < 2 ^ (prefixWord ++ tailWord_5668640).sum := by decide
  have hdescent : baseEnd_5668640 < baseStart_5668640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668644 : List Nat := [2, 3, 1, 3, 2, 2, 3, 1, 1, 5]
def baseStart_5668644 : Nat := 118140960795 + 5668644 * 2 ^ 59
def prefixEnd_5668644 : Nat := 4983230072969 + 3 ^ 40 * 5668644 * 2
def baseEnd_5668644 : Nat := 970246343741808212660129

theorem tailTrace_5668644 : CollatzResearch.WordTrace tailWord_5668644 prefixEnd_5668644 970246343741808212660129 := by
  unfold tailWord_5668644
  simp only [CollatzResearch.WordTrace]
  refine ⟨103376216037739195081878493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137834954716985593442504657 103376216037739195081878493)
  ·
    refine ⟨38766081014152198155704435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103376216037739195081878493 38766081014152198155704435)
    ·
      refine ⟨58149121521228297233556653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38766081014152198155704435 58149121521228297233556653)
      ·
        refine ⟨21805920570460611462583745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58149121521228297233556653 21805920570460611462583745)
        ·
          refine ⟨16354440427845458596937809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21805920570460611462583745 16354440427845458596937809)
          ·
            refine ⟨12265830320884093947703357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16354440427845458596937809 12265830320884093947703357)
            ·
              refine ⟨4599686370331535230388759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12265830320884093947703357 4599686370331535230388759)
              ·
                refine ⟨6899529555497302845583139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4599686370331535230388759 6899529555497302845583139)
                ·
                  refine ⟨10349294333245954268374709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6899529555497302845583139 10349294333245954268374709)
                  ·
                    refine ⟨970246343741808212660129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10349294333245954268374709 970246343741808212660129)
                    ·
                      rfl

theorem cell23_5668644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_5668644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668644 prefixEnd_5668644 := by exact prefixLift 5668644
  have htrace : WordTrace (prefixWord ++ tailWord_5668644) baseStart_5668644 baseEnd_5668644 := by
    simpa [prefixWord, tailWord_5668644, baseEnd_5668644] using wordTrace_append hprefix tailTrace_5668644
  have hstable : (prefixWord ++ tailWord_5668644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668644).length < 2 ^ (prefixWord ++ tailWord_5668644).sum := by decide
  have hdescent : baseEnd_5668644 < baseStart_5668644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668657 : List Nat := [1, 2, 2, 3, 2, 2, 1, 4, 2, 4]
def baseStart_5668657 : Nat := 118140960795 + 5668657 * 2 ^ 59
def prefixEnd_5668657 : Nat := 4983230072969 + 3 ^ 40 * 5668657 * 2
def baseEnd_5668657 : Nat := 970248568824644362372609

theorem tailTrace_5668657 : CollatzResearch.WordTrace tailWord_5668657 prefixEnd_5668657 970248568824644362372609 := by
  unfold tailWord_5668657
  simp only [CollatzResearch.WordTrace]
  refine ⟨206752906224431293383980225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137835270816287528922653483 206752906224431293383980225)
  ·
    refine ⟨155064679668323470037985169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206752906224431293383980225 155064679668323470037985169)
    ·
      refine ⟨116298509751242602528488877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155064679668323470037985169 116298509751242602528488877)
      ·
        refine ⟨43611941156715975948183329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116298509751242602528488877 43611941156715975948183329)
        ·
          refine ⟨32708955867536981961137497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43611941156715975948183329 32708955867536981961137497)
          ·
            refine ⟨24531716900652736470853123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32708955867536981961137497 24531716900652736470853123)
            ·
              refine ⟨36797575350979104706279685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24531716900652736470853123 36797575350979104706279685)
              ·
                refine ⟨6899545378308582132427441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36797575350979104706279685 6899545378308582132427441)
                ·
                  refine ⟨5174659033731436599320581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6899545378308582132427441 5174659033731436599320581)
                  ·
                    refine ⟨970248568824644362372609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5174659033731436599320581 970248568824644362372609)
                    ·
                      rfl

theorem cell23_5668657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_5668657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668657 prefixEnd_5668657 := by exact prefixLift 5668657
  have htrace : WordTrace (prefixWord ++ tailWord_5668657) baseStart_5668657 baseEnd_5668657 := by
    simpa [prefixWord, tailWord_5668657, baseEnd_5668657] using wordTrace_append hprefix tailTrace_5668657
  have hstable : (prefixWord ++ tailWord_5668657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668657).length < 2 ^ (prefixWord ++ tailWord_5668657).sum := by decide
  have hdescent : baseEnd_5668657 < baseStart_5668657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668658 : List Nat := [3, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3]
def baseStart_5668658 : Nat := 118140960795 + 5668658 * 2 ^ 59
def prefixEnd_5668658 : Nat := 4983230072969 + 3 ^ 40 * 5668658 * 2
def baseEnd_5668658 : Nat := 2910746219954587583205323

theorem tailTrace_5668658 : CollatzResearch.WordTrace tailWord_5668658 prefixEnd_5668658 2910746219954587583205323 := by
  unfold tailWord_5668658
  simp only [CollatzResearch.WordTrace]
  refine ⟨51688235674356917638691657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137835295131618447036511085 51688235674356917638691657)
  ·
    refine ⟨38766176755767688229018743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51688235674356917638691657 38766176755767688229018743)
    ·
      refine ⟨58149265133651532343528115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38766176755767688229018743 58149265133651532343528115)
      ·
        refine ⟨87223897700477298515292173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58149265133651532343528115 87223897700477298515292173)
        ·
          refine ⟨32708961637678986943234565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87223897700477298515292173 32708961637678986943234565)
          ·
            refine ⟨6132930307064810051856481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32708961637678986943234565 6132930307064810051856481)
            ·
              refine ⟨4599697730298607538892361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6132930307064810051856481 4599697730298607538892361)
              ·
                refine ⟨3449773297723955654169271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4599697730298607538892361 3449773297723955654169271)
                ·
                  refine ⟨5174659946585933481253907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3449773297723955654169271 5174659946585933481253907)
                  ·
                    refine ⟨7761989919878900221880861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5174659946585933481253907 7761989919878900221880861)
                    ·
                      refine ⟨2910746219954587583205323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7761989919878900221880861 2910746219954587583205323)
                      ·
                        rfl

theorem cell23_5668658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3].length) (baseStart_5668658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668658 prefixEnd_5668658 := by exact prefixLift 5668658
  have htrace : WordTrace (prefixWord ++ tailWord_5668658) baseStart_5668658 baseEnd_5668658 := by
    simpa [prefixWord, tailWord_5668658, baseEnd_5668658] using wordTrace_append hprefix tailTrace_5668658
  have hstable : (prefixWord ++ tailWord_5668658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668658).length < 2 ^ (prefixWord ++ tailWord_5668658).sum := by decide
  have hdescent : baseEnd_5668658 < baseStart_5668658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668663 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 7]
def baseStart_5668663 : Nat := 118140960795 + 5668663 * 2 ^ 59
def prefixEnd_5668663 : Nat := 4983230072969 + 3 ^ 40 * 5668663 * 2
def baseEnd_5668663 : Nat := 2910748787357860063642799

theorem tailTrace_5668663 : CollatzResearch.WordTrace tailWord_5668663 prefixEnd_5668663 2910748787357860063642799 := by
  unfold tailWord_5668663
  simp only [CollatzResearch.WordTrace]
  refine ⟨206753125062409556408698643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137835416708273037605799095 206753125062409556408698643)
  ·
    refine ⟨310129687593614334613047965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206753125062409556408698643 310129687593614334613047965)
    ·
      refine ⟨116298632847605375479892987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310129687593614334613047965 116298632847605375479892987)
      ·
        refine ⟨174447949271408063219839481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116298632847605375479892987 174447949271408063219839481)
        ·
          refine ⟨130835961953556047414879611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174447949271408063219839481 130835961953556047414879611)
          ·
            refine ⟨196253942930334071122319417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130835961953556047414879611 196253942930334071122319417)
            ·
              refine ⟨147190457197750553341739563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196253942930334071122319417 147190457197750553341739563)
              ·
                refine ⟨220785685796625830012609345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147190457197750553341739563 220785685796625830012609345)
                ·
                  refine ⟨165589264347469372509457009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220785685796625830012609345 165589264347469372509457009)
                  ·
                    refine ⟨124191948260602029382092757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 165589264347469372509457009 124191948260602029382092757)
                    ·
                      refine ⟨2910748787357860063642799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124191948260602029382092757 2910748787357860063642799)
                      ·
                        rfl

theorem cell23_5668663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_5668663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668663 prefixEnd_5668663 := by exact prefixLift 5668663
  have htrace : WordTrace (prefixWord ++ tailWord_5668663) baseStart_5668663 baseEnd_5668663 := by
    simpa [prefixWord, tailWord_5668663, baseEnd_5668663] using wordTrace_append hprefix tailTrace_5668663
  have hstable : (prefixWord ++ tailWord_5668663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668663).length < 2 ^ (prefixWord ++ tailWord_5668663).sum := by decide
  have hdescent : baseEnd_5668663 < baseStart_5668663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668697 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 4, 1, 3]
def baseStart_5668697 : Nat := 118140960795 + 5668697 * 2 ^ 59
def prefixEnd_5668697 : Nat := 4983230072969 + 3 ^ 40 * 5668697 * 2
def baseEnd_5668697 : Nat := 2910766245700112930617643

theorem tailTrace_5668697 : CollatzResearch.WordTrace tailWord_5668697 prefixEnd_5668697 2910766245700112930617643 := by
  unfold tailWord_5668697
  simp only [CollatzResearch.WordTrace]
  refine ⟨206754365144286380215436345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137836243429524253476957563 206754365144286380215436345)
  ·
    refine ⟨155065773858214785161577259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206754365144286380215436345 155065773858214785161577259)
    ·
      refine ⟨232598660787322177742365889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155065773858214785161577259 232598660787322177742365889)
      ·
        refine ⟨174448995590491633306774417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232598660787322177742365889 174448995590491633306774417)
        ·
          refine ⟨130836746692868724980080813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174448995590491633306774417 130836746692868724980080813)
          ·
            refine ⟨49063780009825771867530305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130836746692868724980080813 49063780009825771867530305)
            ·
              refine ⟨36797835007369328900647729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49063780009825771867530305 36797835007369328900647729)
              ·
                refine ⟨27598376255526996675485797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36797835007369328900647729 27598376255526996675485797)
                ·
                  refine ⟨5174695547911311876653587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27598376255526996675485797 5174695547911311876653587)
                  ·
                    refine ⟨7762043321866967814980381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5174695547911311876653587 7762043321866967814980381)
                    ·
                      refine ⟨2910766245700112930617643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7762043321866967814980381 2910766245700112930617643)
                      ·
                        rfl

theorem cell23_5668697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 4, 1, 3].length) (baseStart_5668697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668697 prefixEnd_5668697 := by exact prefixLift 5668697
  have htrace : WordTrace (prefixWord ++ tailWord_5668697) baseStart_5668697 baseEnd_5668697 := by
    simpa [prefixWord, tailWord_5668697, baseEnd_5668697] using wordTrace_append hprefix tailTrace_5668697
  have hstable : (prefixWord ++ tailWord_5668697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668697).length < 2 ^ (prefixWord ++ tailWord_5668697).sum := by decide
  have hdescent : baseEnd_5668697 < baseStart_5668697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668730 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 2, 6]
def baseStart_5668730 : Nat := 118140960795 + 5668730 * 2 ^ 59
def prefixEnd_5668730 : Nat := 4983230072969 + 3 ^ 40 * 5668730 * 2
def baseEnd_5668730 : Nat := 970261063520570433834997

theorem tailTrace_5668730 : CollatzResearch.WordTrace tailWord_5668730 prefixEnd_5668730 970261063520570433834997 := by
  unfold tailWord_5668730
  simp only [CollatzResearch.WordTrace]
  refine ⟨51688892188291706712846911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137837045835444551234258429 51688892188291706712846911)
  ·
    refine ⟨77533338282437560069270367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51688892188291706712846911 77533338282437560069270367)
    ·
      refine ⟨116300007423656340103905551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77533338282437560069270367 116300007423656340103905551)
      ·
        refine ⟨174450011135484510155858327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116300007423656340103905551 174450011135484510155858327)
        ·
          refine ⟨261675016703226765233787491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174450011135484510155858327 261675016703226765233787491)
          ·
            refine ⟨392512525054840147850681237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261675016703226765233787491 392512525054840147850681237)
            ·
              refine ⟨18399024611945631930500683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 392512525054840147850681237 18399024611945631930500683)
              ·
                refine ⟨27598536917918447895751025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18399024611945631930500683 27598536917918447895751025)
                ·
                  refine ⟨20698902688438835921813269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27598536917918447895751025 20698902688438835921813269)
                  ·
                    refine ⟨970261063520570433834997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20698902688438835921813269 970261063520570433834997)
                    ·
                      rfl

theorem cell23_5668730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_5668730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668730 prefixEnd_5668730 := by exact prefixLift 5668730
  have htrace : WordTrace (prefixWord ++ tailWord_5668730) baseStart_5668730 baseEnd_5668730 := by
    simpa [prefixWord, tailWord_5668730, baseEnd_5668730] using wordTrace_append hprefix tailTrace_5668730
  have hstable : (prefixWord ++ tailWord_5668730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668730).length < 2 ^ (prefixWord ++ tailWord_5668730).sum := by decide
  have hdescent : baseEnd_5668730 < baseStart_5668730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668800 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 7]
def baseStart_5668800 : Nat := 118140960795 + 5668800 * 2 ^ 59
def prefixEnd_5668800 : Nat := 4983230072969 + 3 ^ 40 * 5668800 * 2
def baseEnd_5668800 : Nat := 2910819134207526027629669

theorem tailTrace_5668800 : CollatzResearch.WordTrace tailWord_5668800 prefixEnd_5668800 2910819134207526027629669 := by
  unfold tailWord_5668800
  simp only [CollatzResearch.WordTrace]
  refine ⟨103379060931456614403217927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137838747908608819204290569 103379060931456614403217927)
  ·
    refine ⟨155068591397184921604826891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103379060931456614403217927 155068591397184921604826891)
    ·
      refine ⟨232602887095777382407240337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155068591397184921604826891 232602887095777382407240337)
      ·
        refine ⟨174452165321833036805430253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232602887095777382407240337 174452165321833036805430253)
        ·
          refine ⟨65419561995687388802036345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174452165321833036805430253 65419561995687388802036345)
          ·
            refine ⟨49064671496765541601527259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65419561995687388802036345 49064671496765541601527259)
            ·
              refine ⟨73597007245148312402290889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49064671496765541601527259 73597007245148312402290889)
              ·
                refine ⟨55197755433861234301718167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73597007245148312402290889 55197755433861234301718167)
                ·
                  refine ⟨82796633150791851452577251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55197755433861234301718167 82796633150791851452577251)
                  ·
                    refine ⟨124194949726187777178865877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82796633150791851452577251 124194949726187777178865877)
                    ·
                      refine ⟨2910819134207526027629669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124194949726187777178865877 2910819134207526027629669)
                      ·
                        rfl

theorem cell23_5668800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_5668800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668800 prefixEnd_5668800 := by exact prefixLift 5668800
  have htrace : WordTrace (prefixWord ++ tailWord_5668800) baseStart_5668800 baseEnd_5668800 := by
    simpa [prefixWord, tailWord_5668800, baseEnd_5668800] using wordTrace_append hprefix tailTrace_5668800
  have hstable : (prefixWord ++ tailWord_5668800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668800).length < 2 ^ (prefixWord ++ tailWord_5668800).sum := by decide
  have hdescent : baseEnd_5668800 < baseStart_5668800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668847 : List Nat := [1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 3]
def baseStart_5668847 : Nat := 118140960795 + 5668847 * 2 ^ 59
def prefixEnd_5668847 : Nat := 4983230072969 + 3 ^ 40 * 5668847 * 2
def baseEnd_5668847 : Nat := 2910843267798287343741953

theorem tailTrace_5668847 : CollatzResearch.WordTrace tailWord_5668847 prefixEnd_5668847 2910843267798287343741953 := by
  unfold tailWord_5668847
  simp only [CollatzResearch.WordTrace]
  refine ⟨206759836093742955833396795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137839890729161970555597863 206759836093742955833396795)
  ·
    refine ⟨310139754140614433750095193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206759836093742955833396795 310139754140614433750095193)
    ·
      refine ⟨232604815605460825312571395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310139754140614433750095193 232604815605460825312571395)
      ·
        refine ⟨348907223408191237968857093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232604815605460825312571395 348907223408191237968857093)
        ·
          refine ⟨65420104389035857119160705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 348907223408191237968857093 65420104389035857119160705)
          ·
            refine ⟨49065078291776892839370529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65420104389035857119160705 49065078291776892839370529)
            ·
              refine ⟨36798808718832669629527897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49065078291776892839370529 36798808718832669629527897)
              ·
                refine ⟨27599106539124502222145923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36798808718832669629527897 27599106539124502222145923)
                ·
                  refine ⟨41398659808686753333218885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27599106539124502222145923 41398659808686753333218885)
                  ·
                    refine ⟨7762248714128766249978541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41398659808686753333218885 7762248714128766249978541)
                    ·
                      refine ⟨2910843267798287343741953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7762248714128766249978541 2910843267798287343741953)
                      ·
                        rfl

theorem cell23_5668847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 3].length) (baseStart_5668847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668847 prefixEnd_5668847 := by exact prefixLift 5668847
  have htrace : WordTrace (prefixWord ++ tailWord_5668847) baseStart_5668847 baseEnd_5668847 := by
    simpa [prefixWord, tailWord_5668847, baseEnd_5668847] using wordTrace_append hprefix tailTrace_5668847
  have hstable : (prefixWord ++ tailWord_5668847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668847).length < 2 ^ (prefixWord ++ tailWord_5668847).sum := by decide
  have hdescent : baseEnd_5668847 < baseStart_5668847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668871 : List Nat := [1, 1, 4, 3, 1, 2, 1, 5, 1, 4]
def baseStart_5668871 : Nat := 118140960795 + 5668871 * 2 ^ 59
def prefixEnd_5668871 : Nat := 4983230072969 + 3 ^ 40 * 5668871 * 2
def baseEnd_5668871 : Nat := 970285197111331749947281

theorem tailTrace_5668871 : CollatzResearch.WordTrace tailWord_5668871 prefixEnd_5668871 970285197111331749947281 := by
  unfold tailWord_5668871
  simp only [CollatzResearch.WordTrace]
  refine ⟨206760711445656007932270467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137840474297104005288180311 206760711445656007932270467)
  ·
    refine ⟨310141067168484011898405701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206760711445656007932270467 310141067168484011898405701)
    ·
      refine ⟨58151450094090752230951069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310141067168484011898405701 58151450094090752230951069)
      ·
        refine ⟨21806793785284032086606651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58151450094090752230951069 21806793785284032086606651)
        ·
          refine ⟨32710190677926048129909977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21806793785284032086606651 32710190677926048129909977)
          ·
            refine ⟨24532643008444536097432483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32710190677926048129909977 24532643008444536097432483)
            ·
              refine ⟨36798964512666804146148725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24532643008444536097432483 36798964512666804146148725)
              ·
                refine ⟨3449902923062512888701443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36798964512666804146148725 3449902923062512888701443)
                ·
                  refine ⟨5174854384593769333052165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3449902923062512888701443 5174854384593769333052165)
                  ·
                    refine ⟨970285197111331749947281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5174854384593769333052165 970285197111331749947281)
                    ·
                      rfl

theorem cell23_5668871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_5668871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668871 prefixEnd_5668871 := by exact prefixLift 5668871
  have htrace : WordTrace (prefixWord ++ tailWord_5668871) baseStart_5668871 baseEnd_5668871 := by
    simpa [prefixWord, tailWord_5668871, baseEnd_5668871] using wordTrace_append hprefix tailTrace_5668871
  have hstable : (prefixWord ++ tailWord_5668871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668871).length < 2 ^ (prefixWord ++ tailWord_5668871).sum := by decide
  have hdescent : baseEnd_5668871 < baseStart_5668871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668914 : List Nat := [3, 2, 1, 1, 2, 3, 1, 4, 1, 5]
def baseStart_5668914 : Nat := 118140960795 + 5668914 * 2 ^ 59
def prefixEnd_5668914 : Nat := 4983230072969 + 3 ^ 40 * 5668914 * 2
def baseEnd_5668914 : Nat := 970292557000712860534715

theorem tailTrace_5668914 : CollatzResearch.WordTrace tailWord_5668914 prefixEnd_5668914 970292557000712860534715 := by
  unfold tailWord_5668914
  simp only [CollatzResearch.WordTrace]
  refine ⟨51690569946125056569021449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137841519856333484184057197 51690569946125056569021449)
  ·
    refine ⟨38767927459593792426766087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51690569946125056569021449 38767927459593792426766087)
    ·
      refine ⟨58151891189390688640149131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38767927459593792426766087 58151891189390688640149131)
      ·
        refine ⟨87227836784086032960223697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58151891189390688640149131 87227836784086032960223697)
        ·
          refine ⟨65420877588064524720167773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87227836784086032960223697 65420877588064524720167773)
          ·
            refine ⟨24532829095524196770062915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65420877588064524720167773 24532829095524196770062915)
            ·
              refine ⟨36799243643286295155094373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24532829095524196770062915 36799243643286295155094373)
              ·
                refine ⟨6899858183116180341580195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36799243643286295155094373 6899858183116180341580195)
                ·
                  refine ⟨10349787274674270512370293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6899858183116180341580195 10349787274674270512370293)
                  ·
                    refine ⟨970292557000712860534715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10349787274674270512370293 970292557000712860534715)
                    ·
                      rfl

theorem cell23_5668914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_5668914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668914 prefixEnd_5668914 := by exact prefixLift 5668914
  have htrace : WordTrace (prefixWord ++ tailWord_5668914) baseStart_5668914 baseEnd_5668914 := by
    simpa [prefixWord, tailWord_5668914, baseEnd_5668914] using wordTrace_append hprefix tailTrace_5668914
  have hstable : (prefixWord ++ tailWord_5668914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668914).length < 2 ^ (prefixWord ++ tailWord_5668914).sum := by decide
  have hdescent : baseEnd_5668914 < baseStart_5668914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668927 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 1, 6]
def baseStart_5668927 : Nat := 118140960795 + 5668927 * 2 ^ 59
def prefixEnd_5668927 : Nat := 4983230072969 + 3 ^ 40 * 5668927 * 2
def baseEnd_5668927 : Nat := 970294782083549010247195

theorem tailTrace_5668927 : CollatzResearch.WordTrace tailWord_5668927 prefixEnd_5668927 970294782083549010247195 := by
  unfold tailWord_5668927
  simp only [CollatzResearch.WordTrace]
  refine ⟨206762753933453129496309035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137841835955635419664206023 206762753933453129496309035)
  ·
    refine ⟨310144130900179694244463553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206762753933453129496309035 310144130900179694244463553)
    ·
      refine ⟨232608098175134770683347665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310144130900179694244463553 232608098175134770683347665)
      ·
        refine ⟨174456073631351078012510749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232608098175134770683347665 174456073631351078012510749)
        ·
          refine ⟨65421027611756654254691531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174456073631351078012510749 65421027611756654254691531)
          ·
            refine ⟨98131541417634981382037297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65421027611756654254691531 98131541417634981382037297)
            ·
              refine ⟨73598656063226236036527973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98131541417634981382037297 73598656063226236036527973)
              ·
                refine ⟨13799748011854919256848995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73598656063226236036527973 13799748011854919256848995)
                ·
                  refine ⟨20699622017782378885273493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13799748011854919256848995 20699622017782378885273493)
                  ·
                    refine ⟨970294782083549010247195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20699622017782378885273493 970294782083549010247195)
                    ·
                      rfl

theorem cell23_5668927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 6].length) (baseStart_5668927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668927 prefixEnd_5668927 := by exact prefixLift 5668927
  have htrace : WordTrace (prefixWord ++ tailWord_5668927) baseStart_5668927 baseEnd_5668927 := by
    simpa [prefixWord, tailWord_5668927, baseEnd_5668927] using wordTrace_append hprefix tailTrace_5668927
  have hstable : (prefixWord ++ tailWord_5668927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668927).length < 2 ^ (prefixWord ++ tailWord_5668927).sum := by decide
  have hdescent : baseEnd_5668927 < baseStart_5668927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668928 : List Nat := [2, 1, 1, 2, 2, 4, 3, 3, 1, 1, 3]
def baseStart_5668928 : Nat := 118140960795 + 5668928 * 2 ^ 59
def prefixEnd_5668928 : Nat := 4983230072969 + 3 ^ 40 * 5668928 * 2
def baseEnd_5668928 : Nat := 2910884859731301526829081

theorem tailTrace_5668928 : CollatzResearch.WordTrace tailWord_5668928 prefixEnd_5668928 2910884859731301526829081 := by
  unfold tailWord_5668928
  simp only [CollatzResearch.WordTrace]
  refine ⟨103381395203224753333547719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137841860270966337778063625 103381395203224753333547719)
  ·
    refine ⟨155072092804837130000321579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103381395203224753333547719 155072092804837130000321579)
    ·
      refine ⟨232608139207255695000482369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155072092804837130000321579 232608139207255695000482369)
      ·
        refine ⟨174456104405441771250361777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232608139207255695000482369 174456104405441771250361777)
        ·
          refine ⟨130842078304081328437771333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174456104405441771250361777 130842078304081328437771333)
          ·
            refine ⟨24532889682015249082082125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130842078304081328437771333 24532889682015249082082125)
            ·
              refine ⟨9199833630755718405780797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24532889682015249082082125 9199833630755718405780797)
              ·
                refine ⟨3449937611533394402167799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9199833630755718405780797 3449937611533394402167799)
                ·
                  refine ⟨5174906417300091603251699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3449937611533394402167799 5174906417300091603251699)
                  ·
                    refine ⟨7762359625950137404877549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5174906417300091603251699 7762359625950137404877549)
                    ·
                      refine ⟨2910884859731301526829081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7762359625950137404877549 2910884859731301526829081)
                      ·
                        rfl

theorem cell23_5668928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 3, 1, 1, 3].length) (baseStart_5668928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668928 prefixEnd_5668928 := by exact prefixLift 5668928
  have htrace : WordTrace (prefixWord ++ tailWord_5668928) baseStart_5668928 baseEnd_5668928 := by
    simpa [prefixWord, tailWord_5668928, baseEnd_5668928] using wordTrace_append hprefix tailTrace_5668928
  have hstable : (prefixWord ++ tailWord_5668928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668928).length < 2 ^ (prefixWord ++ tailWord_5668928).sum := by decide
  have hdescent : baseEnd_5668928 < baseStart_5668928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668954 : List Nat := [3, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3]
def baseStart_5668954 : Nat := 118140960795 + 5668954 * 2 ^ 59
def prefixEnd_5668954 : Nat := 4983230072969 + 3 ^ 40 * 5668954 * 2
def baseEnd_5668954 : Nat := 2910898210228318425103961

theorem tailTrace_5668954 : CollatzResearch.WordTrace tailWord_5668954 prefixEnd_5668954 2910898210228318425103961 := by
  unfold tailWord_5668954
  simp only [CollatzResearch.WordTrace]
  refine ⟨51690934676088828276885479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137842492469570208738361277 51690934676088828276885479)
  ·
    refine ⟨77536402014133242415328219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51690934676088828276885479 77536402014133242415328219)
    ·
      refine ⟨116304603021199863622992329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77536402014133242415328219 116304603021199863622992329)
      ·
        refine ⟨87228452265899897717244247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116304603021199863622992329 87228452265899897717244247)
        ·
          refine ⟨130842678398849846575866371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87228452265899897717244247 130842678398849846575866371)
          ·
            refine ⟨196264017598274769863799557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130842678398849846575866371 196264017598274769863799557)
            ·
              refine ⟨36799503299676519349462417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196264017598274769863799557 36799503299676519349462417)
              ·
                refine ⟨27599627474757389512096813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36799503299676519349462417 27599627474757389512096813)
                ·
                  refine ⟨10349860303034021067036305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27599627474757389512096813 10349860303034021067036305)
                  ·
                    refine ⟨7762395227275515800277229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10349860303034021067036305 7762395227275515800277229)
                    ·
                      refine ⟨2910898210228318425103961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7762395227275515800277229 2910898210228318425103961)
                      ·
                        rfl

theorem cell23_5668954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_5668954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668954 prefixEnd_5668954 := by exact prefixLift 5668954
  have htrace : WordTrace (prefixWord ++ tailWord_5668954) baseStart_5668954 baseEnd_5668954 := by
    simpa [prefixWord, tailWord_5668954, baseEnd_5668954] using wordTrace_append hprefix tailTrace_5668954
  have hstable : (prefixWord ++ tailWord_5668954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668954).length < 2 ^ (prefixWord ++ tailWord_5668954).sum := by decide
  have hdescent : baseEnd_5668954 < baseStart_5668954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5668988 : List Nat := [2, 2, 2, 1, 1, 5, 3, 1, 1, 2, 3]
def baseStart_5668988 : Nat := 118140960795 + 5668988 * 2 ^ 59
def prefixEnd_5668988 : Nat := 4983230072969 + 3 ^ 40 * 5668988 * 2
def baseEnd_5668988 : Nat := 2910915668570571292078805

theorem tailTrace_5668988 : CollatzResearch.WordTrace tailWord_5668988 prefixEnd_5668988 2910915668570571292078805 := by
  unfold tailWord_5668988
  simp only [CollatzResearch.WordTrace]
  refine ⟨103382489393116068457139809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137843319190821424609519745 103382489393116068457139809)
  ·
    refine ⟨77536867044837051342854857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103382489393116068457139809 77536867044837051342854857)
    ·
      refine ⟨58152650283627788507141143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77536867044837051342854857 58152650283627788507141143)
      ·
        refine ⟨87228975425441682760711715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58152650283627788507141143 87228975425441682760711715)
        ·
          refine ⟨130843463138162524141067573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87228975425441682760711715 130843463138162524141067573)
          ·
            refine ⟨12266574669202736638225085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 130843463138162524141067573 12266574669202736638225085)
            ·
              refine ⟨4599965500951026239334407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12266574669202736638225085 4599965500951026239334407)
              ·
                refine ⟨6899948251426539359001611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4599965500951026239334407 6899948251426539359001611)
                ·
                  refine ⟨10349922377139809038502417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6899948251426539359001611 10349922377139809038502417)
                  ·
                    refine ⟨7762441782854856778876813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10349922377139809038502417 7762441782854856778876813)
                    ·
                      refine ⟨2910915668570571292078805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7762441782854856778876813 2910915668570571292078805)
                      ·
                        rfl

theorem cell23_5668988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_5668988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5668988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5668988 prefixEnd_5668988 := by exact prefixLift 5668988
  have htrace : WordTrace (prefixWord ++ tailWord_5668988) baseStart_5668988 baseEnd_5668988 := by
    simpa [prefixWord, tailWord_5668988, baseEnd_5668988] using wordTrace_append hprefix tailTrace_5668988
  have hstable : (prefixWord ++ tailWord_5668988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5668988).length < 2 ^ (prefixWord ++ tailWord_5668988).sum := by decide
  have hdescent : baseEnd_5668988 < baseStart_5668988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5668988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669002 : List Nat := [3, 1, 2, 3, 1, 2, 4, 2, 1, 2, 2]
def baseStart_5669002 : Nat := 118140960795 + 5669002 * 2 ^ 59
def prefixEnd_5669002 : Nat := 4983230072969 + 3 ^ 40 * 5669002 * 2
def baseEnd_5669002 : Nat := 2910922857299734237303741

theorem tailTrace_5669002 : CollatzResearch.WordTrace tailWord_5669002 prefixEnd_5669002 2910922857299734237303741 := by
  unfold tailWord_5669002
  simp only [CollatzResearch.WordTrace]
  refine ⟨51691372352045354326322315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137843659605454278203526173 51691372352045354326322315)
  ·
    refine ⟨77537058528068031489483473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51691372352045354326322315 77537058528068031489483473)
    ·
      refine ⟨58152793896051023617112605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77537058528068031489483473 58152793896051023617112605)
      ·
        refine ⟨21807297711019133856417227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58152793896051023617112605 21807297711019133856417227)
        ·
          refine ⟨32710946566528700784625841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21807297711019133856417227 32710946566528700784625841)
          ·
            refine ⟨24533209924896525588469381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32710946566528700784625841 24533209924896525588469381)
            ·
              refine ⟨4599976860918098547838009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24533209924896525588469381 4599976860918098547838009)
              ·
                refine ⟨3449982645688573910878507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4599976860918098547838009 3449982645688573910878507)
                ·
                  refine ⟨5174973968532860866317761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3449982645688573910878507 5174973968532860866317761)
                  ·
                    refine ⟨3881230476399645649738321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5174973968532860866317761 3881230476399645649738321)
                    ·
                      refine ⟨2910922857299734237303741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3881230476399645649738321 2910922857299734237303741)
                      ·
                        rfl

theorem cell23_5669002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_5669002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669002 prefixEnd_5669002 := by exact prefixLift 5669002
  have htrace : WordTrace (prefixWord ++ tailWord_5669002) baseStart_5669002 baseEnd_5669002 := by
    simpa [prefixWord, tailWord_5669002, baseEnd_5669002] using wordTrace_append hprefix tailTrace_5669002
  have hstable : (prefixWord ++ tailWord_5669002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669002).length < 2 ^ (prefixWord ++ tailWord_5669002).sum := by decide
  have hdescent : baseEnd_5669002 < baseStart_5669002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669018 : List Nat := [3, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3]
def baseStart_5669018 : Nat := 118140960795 + 5669018 * 2 ^ 59
def prefixEnd_5669018 : Nat := 4983230072969 + 3 ^ 40 * 5669018 * 2
def baseEnd_5669018 : Nat := 2910931072990206174703667

theorem tailTrace_5669018 : CollatzResearch.WordTrace tailWord_5669018 prefixEnd_5669018 2910931072990206174703667 := by
  unfold tailWord_5669018
  simp only [CollatzResearch.WordTrace]
  refine ⟨51691518244030863009467927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137844048650748968025247805 51691518244030863009467927)
  ·
    refine ⟨77537277366046294514201891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51691518244030863009467927 77537277366046294514201891)
    ·
      refine ⟨116305916049069441771302837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77537277366046294514201891 116305916049069441771302837)
      ·
        refine ⟨10903679629600260166059641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116305916049069441771302837 10903679629600260166059641)
        ·
          refine ⟨8177759722200195124544731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10903679629600260166059641 8177759722200195124544731)
          ·
            refine ⟨12266639583300292686817097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8177759722200195124544731 12266639583300292686817097)
            ·
              refine ⟨9199979687475219515112823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12266639583300292686817097 9199979687475219515112823)
              ·
                refine ⟨13799969531212829272669235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9199979687475219515112823 13799969531212829272669235)
                ·
                  refine ⟨20699954296819243909003853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13799969531212829272669235 20699954296819243909003853)
                  ·
                    refine ⟨7762482861307216465876445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20699954296819243909003853 7762482861307216465876445)
                    ·
                      refine ⟨2910931072990206174703667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7762482861307216465876445 2910931072990206174703667)
                      ·
                        rfl

theorem cell23_5669018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_5669018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669018 prefixEnd_5669018 := by exact prefixLift 5669018
  have htrace : WordTrace (prefixWord ++ tailWord_5669018) baseStart_5669018 baseEnd_5669018 := by
    simpa [prefixWord, tailWord_5669018, baseEnd_5669018] using wordTrace_append hprefix tailTrace_5669018
  have hstable : (prefixWord ++ tailWord_5669018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669018).length < 2 ^ (prefixWord ++ tailWord_5669018).sum := by decide
  have hdescent : baseEnd_5669018 < baseStart_5669018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669052 : List Nat := [2, 2, 2, 3, 4, 1, 1, 2, 2, 1, 3]
def baseStart_5669052 : Nat := 118140960795 + 5669052 * 2 ^ 59
def prefixEnd_5669052 : Nat := 4983230072969 + 3 ^ 40 * 5669052 * 2
def baseEnd_5669052 : Nat := 2910948531332459041678511

theorem tailTrace_5669052 : CollatzResearch.WordTrace tailWord_5669052 prefixEnd_5669052 2910948531332459041678511 := by
  unfold tailWord_5669052
  simp only [CollatzResearch.WordTrace]
  refine ⟨103383656529000137922304705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137844875372000183896406273 103383656529000137922304705)
  ·
    refine ⟨77537742396750103441728529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103383656529000137922304705 77537742396750103441728529)
    ·
      refine ⟨58153306797562577581296397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77537742396750103441728529 58153306797562577581296397)
      ·
        refine ⟨21807490049085966592986149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58153306797562577581296397 21807490049085966592986149)
        ·
          refine ⟨4088904384203618736184903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21807490049085966592986149 4088904384203618736184903)
          ·
            refine ⟨6133356576305428104277355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4088904384203618736184903 6133356576305428104277355)
            ·
              refine ⟨9200034864458142156416033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6133356576305428104277355 9200034864458142156416033)
              ·
                refine ⟨6900026148343606617312025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9200034864458142156416033 6900026148343606617312025)
                ·
                  refine ⟨5175019611257704962984019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6900026148343606617312025 5175019611257704962984019)
                  ·
                    refine ⟨7762529416886557444476029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5175019611257704962984019 7762529416886557444476029)
                    ·
                      refine ⟨2910948531332459041678511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7762529416886557444476029 2910948531332459041678511)
                      ·
                        rfl

theorem cell23_5669052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_5669052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669052 prefixEnd_5669052 := by exact prefixLift 5669052
  have htrace : WordTrace (prefixWord ++ tailWord_5669052) baseStart_5669052 baseEnd_5669052 := by
    simpa [prefixWord, tailWord_5669052, baseEnd_5669052] using wordTrace_append hprefix tailTrace_5669052
  have hstable : (prefixWord ++ tailWord_5669052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669052).length < 2 ^ (prefixWord ++ tailWord_5669052).sum := by decide
  have hdescent : baseEnd_5669052 < baseStart_5669052 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669118 : List Nat := [4, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2]
def baseStart_5669118 : Nat := 118140960795 + 5669118 * 2 ^ 59
def prefixEnd_5669118 : Nat := 4983230072969 + 3 ^ 40 * 5669118 * 2
def baseEnd_5669118 : Nat := 2910982421055655783453207

theorem tailTrace_5669118 : CollatzResearch.WordTrace tailWord_5669118 prefixEnd_5669118 2910982421055655783453207 := by
  unfold tailWord_5669118
  simp only [CollatzResearch.WordTrace]
  refine ⟨25846215034470146139564001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137846480183840779411008005 25846215034470146139564001)
  ·
    refine ⟨19384661275852609604673001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25846215034470146139564001 19384661275852609604673001)
    ·
      refine ⟨14538495956889457203504751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19384661275852609604673001 14538495956889457203504751)
      ·
        refine ⟨21807743935334185805257127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14538495956889457203504751 21807743935334185805257127)
        ·
          refine ⟨32711615903001278707885691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21807743935334185805257127 32711615903001278707885691)
          ·
            refine ⟨49067423854501918061828537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32711615903001278707885691 49067423854501918061828537)
            ·
              refine ⟨36800567890876438546371403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49067423854501918061828537 36800567890876438546371403)
              ·
                refine ⟨55200851836314657819557105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36800567890876438546371403 55200851836314657819557105)
                ·
                  refine ⟨41400638877235993364667829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55200851836314657819557105 41400638877235993364667829)
                  ·
                    refine ⟨3881309894740874377937609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41400638877235993364667829 3881309894740874377937609)
                    ·
                      refine ⟨2910982421055655783453207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3881309894740874377937609 2910982421055655783453207)
                      ·
                        rfl

theorem cell23_5669118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_5669118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669118 prefixEnd_5669118 := by exact prefixLift 5669118
  have htrace : WordTrace (prefixWord ++ tailWord_5669118) baseStart_5669118 baseEnd_5669118 := by
    simpa [prefixWord, tailWord_5669118, baseEnd_5669118] using wordTrace_append hprefix tailTrace_5669118
  have hstable : (prefixWord ++ tailWord_5669118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669118).length < 2 ^ (prefixWord ++ tailWord_5669118).sum := by decide
  have hdescent : baseEnd_5669118 < baseStart_5669118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669131 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 1, 6, 2]
def baseStart_5669131 : Nat := 118140960795 + 5669131 * 2 ^ 59
def prefixEnd_5669131 : Nat := 4983230072969 + 3 ^ 40 * 5669131 * 2
def baseEnd_5669131 : Nat := 2910989096304164232590647

theorem tailTrace_5669131 : CollatzResearch.WordTrace tailWord_5669131 prefixEnd_5669131 2910989096304164232590647 := by
  unfold tailWord_5669131
  simp only [CollatzResearch.WordTrace]
  refine ⟨206770194424714072336735247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137846796283142714891156831 206770194424714072336735247)
  ·
    refine ⟨310155291637071108505102871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206770194424714072336735247 310155291637071108505102871)
    ·
      refine ⟨465232937455606662757654307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310155291637071108505102871 465232937455606662757654307)
      ·
        refine ⟨697849406183409994136481461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465232937455606662757654307 697849406183409994136481461)
        ·
          refine ⟨65423381829694686950295137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 697849406183409994136481461 65423381829694686950295137)
          ·
            refine ⟨49067536372271015212721353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65423381829694686950295137 49067536372271015212721353)
            ·
              refine ⟨36800652279203261409541015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49067536372271015212721353 36800652279203261409541015)
              ·
                refine ⟨55200978418804892114311523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36800652279203261409541015 55200978418804892114311523)
                ·
                  refine ⟨82801467628207338171467285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55200978418804892114311523 82801467628207338171467285)
                  ·
                    refine ⟨3881318795072218976787529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82801467628207338171467285 3881318795072218976787529)
                    ·
                      refine ⟨2910989096304164232590647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3881318795072218976787529 2910989096304164232590647)
                      ·
                        rfl

theorem cell23_5669131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 6, 2].length) (baseStart_5669131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669131 prefixEnd_5669131 := by exact prefixLift 5669131
  have htrace : WordTrace (prefixWord ++ tailWord_5669131) baseStart_5669131 baseEnd_5669131 := by
    simpa [prefixWord, tailWord_5669131, baseEnd_5669131] using wordTrace_append hprefix tailTrace_5669131
  have hstable : (prefixWord ++ tailWord_5669131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669131).length < 2 ^ (prefixWord ++ tailWord_5669131).sum := by decide
  have hdescent : baseEnd_5669131 < baseStart_5669131 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669141 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 3, 4]
def baseStart_5669141 : Nat := 118140960795 + 5669141 * 2 ^ 59
def prefixEnd_5669141 : Nat := 4983230072969 + 3 ^ 40 * 5669141 * 2
def baseEnd_5669141 : Nat := 970331410370236397821867

theorem tailTrace_5669141 : CollatzResearch.WordTrace tailWord_5669141 prefixEnd_5669141 970331410370236397821867 := by
  unfold tailWord_5669141
  simp only [CollatzResearch.WordTrace]
  refine ⟨206770559154677844044599277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137847039436451896029732851 206770559154677844044599277)
  ·
    refine ⟨77538959683004191516724729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206770559154677844044599277 77538959683004191516724729)
    ·
      refine ⟨58154219762253143637543547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77538959683004191516724729 58154219762253143637543547)
      ·
        refine ⟨87231329643379715456315321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58154219762253143637543547 87231329643379715456315321)
        ·
          refine ⟨65423497232534786592236491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87231329643379715456315321 65423497232534786592236491)
          ·
            refine ⟨98135245848802179888354737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65423497232534786592236491 98135245848802179888354737)
            ·
              refine ⟨73601434386601634916266053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98135245848802179888354737 73601434386601634916266053)
              ·
                refine ⟨13800268947487806546799885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73601434386601634916266053 13800268947487806546799885)
                ·
                  refine ⟨5175100855307927455049957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13800268947487806546799885 5175100855307927455049957)
                  ·
                    refine ⟨970331410370236397821867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5175100855307927455049957 970331410370236397821867)
                    ·
                      rfl

theorem cell23_5669141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_5669141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669141 prefixEnd_5669141 := by exact prefixLift 5669141
  have htrace : WordTrace (prefixWord ++ tailWord_5669141) baseStart_5669141 baseEnd_5669141 := by
    simpa [prefixWord, tailWord_5669141, baseEnd_5669141] using wordTrace_append hprefix tailTrace_5669141
  have hstable : (prefixWord ++ tailWord_5669141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669141).length < 2 ^ (prefixWord ++ tailWord_5669141).sum := by decide
  have hdescent : baseEnd_5669141 < baseStart_5669141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669171 : List Nat := [1, 1, 1, 2, 5, 1, 4, 2, 6]
def baseStart_5669171 : Nat := 118140960795 + 5669171 * 2 ^ 59
def prefixEnd_5669171 : Nat := 4983230072969 + 3 ^ 40 * 5669171 * 2
def baseEnd_5669171 : Nat := 323445515058927119565607

theorem tailTrace_5669171 : CollatzResearch.WordTrace tailWord_5669171 prefixEnd_5669171 323445515058927119565607 := by
  unfold tailWord_5669171
  simp only [CollatzResearch.WordTrace]
  refine ⟨206771653344569159168191367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137847768896379439445460911 206771653344569159168191367)
  ·
    refine ⟨310157480016853738752287051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206771653344569159168191367 310157480016853738752287051)
    ·
      refine ⟨465236220025280608128430577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310157480016853738752287051 465236220025280608128430577)
      ·
        refine ⟨348927165018960456096322933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465236220025280608128430577 348927165018960456096322933)
        ·
          refine ⟨32711921720527542759030275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 348927165018960456096322933 32711921720527542759030275)
          ·
            refine ⟨49067882580791314138545413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32711921720527542759030275 49067882580791314138545413)
            ·
              refine ⟨9200227983898371400977265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49067882580791314138545413 9200227983898371400977265)
              ·
                refine ⟨6900170987923778550732949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9200227983898371400977265 6900170987923778550732949)
                ·
                  refine ⟨323445515058927119565607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6900170987923778550732949 323445515058927119565607)
                  ·
                    rfl

theorem cell23_5669171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 2, 6].length) (baseStart_5669171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669171 prefixEnd_5669171 := by exact prefixLift 5669171
  have htrace : WordTrace (prefixWord ++ tailWord_5669171) baseStart_5669171 baseEnd_5669171 := by
    simpa [prefixWord, tailWord_5669171, baseEnd_5669171] using wordTrace_append hprefix tailTrace_5669171
  have hstable : (prefixWord ++ tailWord_5669171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669171).length < 2 ^ (prefixWord ++ tailWord_5669171).sum := by decide
  have hdescent : baseEnd_5669171 < baseStart_5669171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669201 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 3, 5]
def baseStart_5669201 : Nat := 118140960795 + 5669201 * 2 ^ 59
def prefixEnd_5669201 : Nat := 4983230072969 + 3 ^ 40 * 5669201 * 2
def baseEnd_5669201 : Nat := 970341679983326319571775

theorem tailTrace_5669201 : CollatzResearch.WordTrace tailWord_5669201 prefixEnd_5669201 970341679983326319571775 := by
  unfold tailWord_5669201
  simp only [CollatzResearch.WordTrace]
  refine ⟨206772747534460474291783457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137848498356306982861188971 206772747534460474291783457)
  ·
    refine ⟨155079560650845355718837593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206772747534460474291783457 155079560650845355718837593)
    ·
      refine ⟨116309670488134016789128195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155079560650845355718837593 116309670488134016789128195)
      ·
        refine ⟨174464505732201025183692293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116309670488134016789128195 174464505732201025183692293)
        ·
          refine ⟨32712094824787692221942305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174464505732201025183692293 32712094824787692221942305)
          ·
            refine ⟨24534071118590769166456729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32712094824787692221942305 24534071118590769166456729)
            ·
              refine ⟨18400553338943076874842547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24534071118590769166456729 18400553338943076874842547)
              ·
                refine ⟨27600830008414615312263821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18400553338943076874842547 27600830008414615312263821)
                ·
                  refine ⟨10350311253155480742098933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27600830008414615312263821 10350311253155480742098933)
                  ·
                    refine ⟨970341679983326319571775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10350311253155480742098933 970341679983326319571775)
                    ·
                      rfl

theorem cell23_5669201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 5].length) (baseStart_5669201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669201 prefixEnd_5669201 := by exact prefixLift 5669201
  have htrace : WordTrace (prefixWord ++ tailWord_5669201) baseStart_5669201 baseEnd_5669201 := by
    simpa [prefixWord, tailWord_5669201, baseEnd_5669201] using wordTrace_append hprefix tailTrace_5669201
  have hstable : (prefixWord ++ tailWord_5669201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669201).length < 2 ^ (prefixWord ++ tailWord_5669201).sum := by decide
  have hdescent : baseEnd_5669201 < baseStart_5669201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669208 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 2, 3, 2]
def baseStart_5669208 : Nat := 118140960795 + 5669208 * 2 ^ 59
def prefixEnd_5669208 : Nat := 4983230072969 + 3 ^ 40 * 5669208 * 2
def baseEnd_5669208 : Nat := 2911028634314560431327793

theorem tailTrace_5669208 : CollatzResearch.WordTrace tailWord_5669208 prefixEnd_5669208 2911028634314560431327793 := by
  unfold tailWord_5669208
  simp only [CollatzResearch.WordTrace]
  refine ⟨103386501422717557243644139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137848668563623409658192185 103386501422717557243644139)
  ·
    refine ⟨155079752134076335865466209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103386501422717557243644139 155079752134076335865466209)
    ·
      refine ⟨116309814100557251899099657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155079752134076335865466209 116309814100557251899099657)
      ·
        refine ⟨87232360575417938924324743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116309814100557251899099657 87232360575417938924324743)
        ·
          refine ⟨130848540863126908386487115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87232360575417938924324743 130848540863126908386487115)
          ·
            refine ⟨196272811294690362579730673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130848540863126908386487115 196272811294690362579730673)
            ·
              refine ⟨147204608471017771934798005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196272811294690362579730673 147204608471017771934798005)
              ·
                refine ⟨13800432044157916118887313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147204608471017771934798005 13800432044157916118887313)
                ·
                  refine ⟨10350324033118437089165485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13800432044157916118887313 10350324033118437089165485)
                  ·
                    refine ⟨3881371512419413908437057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10350324033118437089165485 3881371512419413908437057)
                    ·
                      refine ⟨2911028634314560431327793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3881371512419413908437057 2911028634314560431327793)
                      ·
                        rfl

theorem cell23_5669208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 2, 3, 2].length) (baseStart_5669208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669208 prefixEnd_5669208 := by exact prefixLift 5669208
  have htrace : WordTrace (prefixWord ++ tailWord_5669208) baseStart_5669208 baseEnd_5669208 := by
    simpa [prefixWord, tailWord_5669208, baseEnd_5669208] using wordTrace_append hprefix tailTrace_5669208
  have hstable : (prefixWord ++ tailWord_5669208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669208).length < 2 ^ (prefixWord ++ tailWord_5669208).sum := by decide
  have hdescent : baseEnd_5669208 < baseStart_5669208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669215 : List Nat := [1, 1, 2, 3, 1, 2, 3, 5, 1, 1, 3]
def baseStart_5669215 : Nat := 118140960795 + 5669215 * 2 ^ 59
def prefixEnd_5669215 : Nat := 4983230072969 + 3 ^ 40 * 5669215 * 2
def baseEnd_5669215 : Nat := 2911032228679141903940261

theorem tailTrace_5669215 : CollatzResearch.WordTrace tailWord_5669215 prefixEnd_5669215 2911032228679141903940261 := by
  unfold tailWord_5669215
  simp only [CollatzResearch.WordTrace]
  refine ⟨206773258156409754682793099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137848838770939836455195399 206773258156409754682793099)
  ·
    refine ⟨310159887234614632024189649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206773258156409754682793099 310159887234614632024189649)
    ·
      refine ⟨232619915425960974018142237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310159887234614632024189649 232619915425960974018142237)
      ·
        refine ⟨87232468284735365256803339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232619915425960974018142237 87232468284735365256803339)
        ·
          refine ⟨130848702427103047885205009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87232468284735365256803339 130848702427103047885205009)
          ·
            refine ⟨98136526820327285913903757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130848702427103047885205009 98136526820327285913903757)
            ·
              refine ⟨36801197557622732217713909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98136526820327285913903757 36801197557622732217713909)
              ·
                refine ⟨3450112271027131145410679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36801197557622732217713909 3450112271027131145410679)
                ·
                  refine ⟨5175168406540696718116019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3450112271027131145410679 5175168406540696718116019)
                  ·
                    refine ⟨7762752609811045077174029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5175168406540696718116019 7762752609811045077174029)
                    ·
                      refine ⟨2911032228679141903940261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7762752609811045077174029 2911032228679141903940261)
                      ·
                        rfl

theorem cell23_5669215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_5669215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669215 prefixEnd_5669215 := by exact prefixLift 5669215
  have htrace : WordTrace (prefixWord ++ tailWord_5669215) baseStart_5669215 baseEnd_5669215 := by
    simpa [prefixWord, tailWord_5669215, baseEnd_5669215] using wordTrace_append hprefix tailTrace_5669215
  have hstable : (prefixWord ++ tailWord_5669215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669215).length < 2 ^ (prefixWord ++ tailWord_5669215).sum := by decide
  have hdescent : baseEnd_5669215 < baseStart_5669215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669255 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 3, 2, 2]
def baseStart_5669255 : Nat := 118140960795 + 5669255 * 2 ^ 59
def prefixEnd_5669255 : Nat := 4983230072969 + 3 ^ 40 * 5669255 * 2
def baseEnd_5669255 : Nat := 2911052767905321747440077

theorem tailTrace_5669255 : CollatzResearch.WordTrace tailWord_5669255 prefixEnd_5669255 2911052767905321747440077 := by
  unfold tailWord_5669255
  simp only [CollatzResearch.WordTrace]
  refine ⟨206774717076264841514249219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137849811384176561009499479 206774717076264841514249219)
  ·
    refine ⟨310162075614397262271373829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206774717076264841514249219 310162075614397262271373829)
    ·
      refine ⟨58155389177699486675882593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310162075614397262271373829 58155389177699486675882593)
      ·
        refine ⟨43616541883274615006911945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58155389177699486675882593 43616541883274615006911945)
        ·
          refine ⟨32712406412455961255183959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43616541883274615006911945 32712406412455961255183959)
          ·
            refine ⟨49068609618683941882775939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32712406412455961255183959 49068609618683941882775939)
            ·
              refine ⟨73602914428025912824163909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49068609618683941882775939 73602914428025912824163909)
              ·
                refine ⟨13800546455254858654530733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73602914428025912824163909 13800546455254858654530733)
                ·
                  refine ⟨5175204920720571995449025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13800546455254858654530733 5175204920720571995449025)
                  ·
                    refine ⟨3881403690540428996586769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5175204920720571995449025 3881403690540428996586769)
                    ·
                      refine ⟨2911052767905321747440077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3881403690540428996586769 2911052767905321747440077)
                      ·
                        rfl

theorem cell23_5669255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_5669255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669255 prefixEnd_5669255 := by exact prefixLift 5669255
  have htrace : WordTrace (prefixWord ++ tailWord_5669255) baseStart_5669255 baseEnd_5669255 := by
    simpa [prefixWord, tailWord_5669255, baseEnd_5669255] using wordTrace_append hprefix tailTrace_5669255
  have hstable : (prefixWord ++ tailWord_5669255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669255).length < 2 ^ (prefixWord ++ tailWord_5669255).sum := by decide
  have hdescent : baseEnd_5669255 < baseStart_5669255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669278 : List Nat := [4, 3, 1, 2, 1, 1, 11]
def baseStart_5669278 : Nat := 118140960795 + 5669278 * 2 ^ 59
def prefixEnd_5669278 : Nat := 4983230072969 + 3 ^ 40 * 5669278 * 2
def baseEnd_5669278 : Nat := 35939068863708335277191

theorem tailTrace_5669278 : CollatzResearch.WordTrace tailWord_5669278 prefixEnd_5669278 35939068863708335277191 := by
  unfold tailWord_5669278
  simp only [CollatzResearch.WordTrace]
  refine ⟨25846944494397689555292061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137850370636787677628224325 25846944494397689555292061)
  ·
    refine ⟨9692604185399133583234523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25846944494397689555292061 9692604185399133583234523)
    ·
      refine ⟨14538906278098700374851785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9692604185399133583234523 14538906278098700374851785)
      ·
        refine ⟨10904179708574025281138839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14538906278098700374851785 10904179708574025281138839)
        ·
          refine ⟨16356269562861037921708259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10904179708574025281138839 16356269562861037921708259)
          ·
            refine ⟨24534404344291556882562389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16356269562861037921708259 24534404344291556882562389)
            ·
              refine ⟨35939068863708335277191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24534404344291556882562389 35939068863708335277191)
              ·
                rfl

theorem cell23_5669278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 11].length) (baseStart_5669278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669278 prefixEnd_5669278 := by exact prefixLift 5669278
  have htrace : WordTrace (prefixWord ++ tailWord_5669278) baseStart_5669278 baseEnd_5669278 := by
    simpa [prefixWord, tailWord_5669278, baseEnd_5669278] using wordTrace_append hprefix tailTrace_5669278
  have hstable : (prefixWord ++ tailWord_5669278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669278).length < 2 ^ (prefixWord ++ tailWord_5669278).sum := by decide
  have hdescent : baseEnd_5669278 < baseStart_5669278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669358 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_5669358 : Nat := 118140960795 + 5669358 * 2 ^ 59
def prefixEnd_5669358 : Nat := 4983230072969 + 3 ^ 40 * 5669358 * 2
def baseEnd_5669358 : Nat := 2911105656412734844452103

theorem tailTrace_5669358 : CollatzResearch.WordTrace tailWord_5669358 prefixEnd_5669358 2911105656412734844452103 := by
  unfold tailWord_5669358
  simp only [CollatzResearch.WordTrace]
  refine ⟨25847309224361461263156091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137852315863261126736832485 25847309224361461263156091)
  ·
    refine ⟨38770963836542191894734137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25847309224361461263156091 38770963836542191894734137)
    ·
      refine ⟨29078222877406643921050603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38770963836542191894734137 29078222877406643921050603)
      ·
        refine ⟨43617334316109965881575905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29078222877406643921050603 43617334316109965881575905)
        ·
          refine ⟨32713000737082474411181929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43617334316109965881575905 32713000737082474411181929)
          ·
            refine ⟨24534750552811855808386447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32713000737082474411181929 24534750552811855808386447)
            ·
              refine ⟨36802125829217783712579671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24534750552811855808386447 36802125829217783712579671)
              ·
                refine ⟨55203188743826675568869507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36802125829217783712579671 55203188743826675568869507)
                ·
                  refine ⟨82804783115740013353304261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55203188743826675568869507 82804783115740013353304261)
                  ·
                    refine ⟨15525896834201252503744549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82804783115740013353304261 15525896834201252503744549)
                    ·
                      refine ⟨2911105656412734844452103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15525896834201252503744549 2911105656412734844452103)
                      ·
                        rfl

theorem cell23_5669358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_5669358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669358 prefixEnd_5669358 := by exact prefixLift 5669358
  have htrace : WordTrace (prefixWord ++ tailWord_5669358) baseStart_5669358 baseEnd_5669358 := by
    simpa [prefixWord, tailWord_5669358, baseEnd_5669358] using wordTrace_append hprefix tailTrace_5669358
  have hstable : (prefixWord ++ tailWord_5669358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669358).length < 2 ^ (prefixWord ++ tailWord_5669358).sum := by decide
  have hdescent : baseEnd_5669358 < baseStart_5669358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669396 : List Nat := [2, 4, 3, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_5669396 : Nat := 118140960795 + 5669396 * 2 ^ 59
def prefixEnd_5669396 : Nat := 4983230072969 + 3 ^ 40 * 5669396 * 2
def baseEnd_5669396 : Nat := 2911125168677605695776929

theorem tailTrace_5669396 : CollatzResearch.WordTrace tailWord_5669396 prefixEnd_5669396 2911125168677605695776929 := by
  unfold tailWord_5669396
  simp only [CollatzResearch.WordTrace]
  refine ⟨103389929884377011297566021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137853239845836015063421361 103389929884377011297566021)
  ·
    refine ⟨19385611853320689618293629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103389929884377011297566021 19385611853320689618293629)
    ·
      refine ⟨7269604444995258606860111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19385611853320689618293629 7269604444995258606860111)
      ·
        refine ⟨10904406667492887910290167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7269604444995258606860111 10904406667492887910290167)
        ·
          refine ⟨16356610001239331865435251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10904406667492887910290167 16356610001239331865435251)
          ·
            refine ⟨24534915001858997798152877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16356610001239331865435251 24534915001858997798152877)
            ·
              refine ⟨9200593125697124174307329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24534915001858997798152877 9200593125697124174307329)
              ·
                refine ⟨6900444844272843130730497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9200593125697124174307329 6900444844272843130730497)
                ·
                  refine ⟨5175333633204632348047873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6900444844272843130730497 5175333633204632348047873)
                  ·
                    refine ⟨3881500224903474261035905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5175333633204632348047873 3881500224903474261035905)
                    ·
                      refine ⟨2911125168677605695776929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3881500224903474261035905 2911125168677605695776929)
                      ·
                        rfl

theorem cell23_5669396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_5669396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669396 prefixEnd_5669396 := by exact prefixLift 5669396
  have htrace : WordTrace (prefixWord ++ tailWord_5669396) baseStart_5669396 baseEnd_5669396 := by
    simpa [prefixWord, tailWord_5669396, baseEnd_5669396] using wordTrace_append hprefix tailTrace_5669396
  have hstable : (prefixWord ++ tailWord_5669396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669396).length < 2 ^ (prefixWord ++ tailWord_5669396).sum := by decide
  have hdescent : baseEnd_5669396 < baseStart_5669396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669458 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 8]
def baseStart_5669458 : Nat := 118140960795 + 5669458 * 2 ^ 59
def prefixEnd_5669458 : Nat := 4983230072969 + 3 ^ 40 * 5669458 * 2
def baseEnd_5669458 : Nat := 323461889386464939244627

theorem tailTrace_5669458 : CollatzResearch.WordTrace tailWord_5669458 prefixEnd_5669458 323461889386464939244627 := by
  unfold tailWord_5669458
  simp only [CollatzResearch.WordTrace]
  refine ⟨51695530273632351795972257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137854747396352938122592685 51695530273632351795972257)
  ·
    refine ⟨38771647705224263846979193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51695530273632351795972257 38771647705224263846979193)
    ·
      refine ⟨29078735778918197885234395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38771647705224263846979193 29078735778918197885234395)
      ·
        refine ⟨43618103668377296827851593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29078735778918197885234395 43618103668377296827851593)
        ·
          refine ⟨32713577751282972620888695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43618103668377296827851593 32713577751282972620888695)
          ·
            refine ⟨49070366626924458931333043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32713577751282972620888695 49070366626924458931333043)
            ·
              refine ⟨73605549940386688396999565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49070366626924458931333043 73605549940386688396999565)
              ·
                refine ⟨27602081227645008148874837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73605549940386688396999565 27602081227645008148874837)
                ·
                  refine ⟨323461889386464939244627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27602081227645008148874837 323461889386464939244627)
                  ·
                    rfl

theorem cell23_5669458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_5669458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669458 prefixEnd_5669458 := by exact prefixLift 5669458
  have htrace : WordTrace (prefixWord ++ tailWord_5669458) baseStart_5669458 baseEnd_5669458 := by
    simpa [prefixWord, tailWord_5669458, baseEnd_5669458] using wordTrace_append hprefix tailTrace_5669458
  have hstable : (prefixWord ++ tailWord_5669458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669458).length < 2 ^ (prefixWord ++ tailWord_5669458).sum := by decide
  have hdescent : baseEnd_5669458 < baseStart_5669458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669495 : List Nat := [1, 1, 3, 1, 1, 3, 2, 3, 1, 5, 2]
def baseStart_5669495 : Nat := 118140960795 + 5669495 * 2 ^ 59
def prefixEnd_5669495 : Nat := 4983230072969 + 3 ^ 40 * 5669495 * 2
def baseEnd_5669495 : Nat := 2911176003262400808438973

theorem tailTrace_5669495 : CollatzResearch.WordTrace tailWord_5669495 prefixEnd_5669495 2911176003262400808438973 := by
  unfold tailWord_5669495
  simp only [CollatzResearch.WordTrace]
  refine ⟨206783470595395362502985939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137855647063596908335323959 206783470595395362502985939)
  ·
    refine ⟨310175205893093043754478909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206783470595395362502985939 310175205893093043754478909)
    ·
      refine ⟨116315702209909891407929591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310175205893093043754478909 116315702209909891407929591)
      ·
        refine ⟨174473553314864837111894387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116315702209909891407929591 174473553314864837111894387)
        ·
          refine ⟨261710329972297255667841581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174473553314864837111894387 261710329972297255667841581)
          ·
            refine ⟨98141373739611470875440593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261710329972297255667841581 98141373739611470875440593)
            ·
              refine ⟨73606030304708603156580445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98141373739611470875440593 73606030304708603156580445)
              ·
                refine ⟨27602261364265726183717667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73606030304708603156580445 27602261364265726183717667)
                ·
                  refine ⟨41403392046398589275576501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27602261364265726183717667 41403392046398589275576501)
                  ·
                    refine ⟨3881568004349867744585297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41403392046398589275576501 3881568004349867744585297)
                    ·
                      refine ⟨2911176003262400808438973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3881568004349867744585297 2911176003262400808438973)
                      ·
                        rfl

theorem cell23_5669495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 5, 2].length) (baseStart_5669495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669495 prefixEnd_5669495 := by exact prefixLift 5669495
  have htrace : WordTrace (prefixWord ++ tailWord_5669495) baseStart_5669495 baseEnd_5669495 := by
    simpa [prefixWord, tailWord_5669495, baseEnd_5669495] using wordTrace_append hprefix tailTrace_5669495
  have hstable : (prefixWord ++ tailWord_5669495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669495).length < 2 ^ (prefixWord ++ tailWord_5669495).sum := by decide
  have hdescent : baseEnd_5669495 < baseStart_5669495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669525 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 4, 6, 2]
def baseStart_5669525 : Nat := 118140960795 + 5669525 * 2 ^ 59
def prefixEnd_5669525 : Nat := 4983230072969 + 3 ^ 40 * 5669525 * 2
def baseEnd_5669525 : Nat := 2911191407682035691063835

theorem tailTrace_5669525 : CollatzResearch.WordTrace tailWord_5669525 prefixEnd_5669525 2911191407682035691063835 := by
  unfold tailWord_5669525
  simp only [CollatzResearch.WordTrace]
  refine ⟨206784564785286677626578029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137856376523524451751052019 206784564785286677626578029)
  ·
    refine ⟨77544211794482504109966761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206784564785286677626578029 77544211794482504109966761)
    ·
      refine ⟨58158158845861878082475071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77544211794482504109966761 58158158845861878082475071)
      ·
        refine ⟨87237238268792817123712607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58158158845861878082475071 87237238268792817123712607)
        ·
          refine ⟨130855857403189225685568911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87237238268792817123712607 130855857403189225685568911)
          ·
            refine ⟨196283786104783838528353367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130855857403189225685568911 196283786104783838528353367)
            ·
              refine ⟨294425679157175757792530051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196283786104783838528353367 294425679157175757792530051)
              ·
                refine ⟨441638518735763636688795077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294425679157175757792530051 441638518735763636688795077)
                ·
                  refine ⟨82807222262955681879149077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 441638518735763636688795077 82807222262955681879149077)
                  ·
                    refine ⟨3881588543576047588085113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82807222262955681879149077 3881588543576047588085113)
                    ·
                      refine ⟨2911191407682035691063835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3881588543576047588085113 2911191407682035691063835)
                      ·
                        rfl

theorem cell23_5669525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_5669525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669525 prefixEnd_5669525 := by exact prefixLift 5669525
  have htrace : WordTrace (prefixWord ++ tailWord_5669525) baseStart_5669525 baseEnd_5669525 := by
    simpa [prefixWord, tailWord_5669525, baseEnd_5669525] using wordTrace_append hprefix tailTrace_5669525
  have hstable : (prefixWord ++ tailWord_5669525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669525).length < 2 ^ (prefixWord ++ tailWord_5669525).sum := by decide
  have hdescent : baseEnd_5669525 < baseStart_5669525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669546 : List Nat := [3, 1, 5, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_5669546 : Nat := 118140960795 + 5669546 * 2 ^ 59
def prefixEnd_5669546 : Nat := 4983230072969 + 3 ^ 40 * 5669546 * 2
def baseEnd_5669546 : Nat := 2911202190775780108901239

theorem tailTrace_5669546 : CollatzResearch.WordTrace tailWord_5669546 prefixEnd_5669546 2911202190775780108901239 := by
  unfold tailWord_5669546
  simp only [CollatzResearch.WordTrace]
  refine ⟨51696332679552649553273123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137856887145473732142061661 51696332679552649553273123)
  ·
    refine ⟨77544499019328974329909685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51696332679552649553273123 77544499019328974329909685)
    ·
      refine ⟨7269796783062091343429033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77544499019328974329909685 7269796783062091343429033)
      ·
        refine ⟨5452347587296568507571775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7269796783062091343429033 5452347587296568507571775)
        ·
          refine ⟨8178521380944852761357663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5452347587296568507571775 8178521380944852761357663)
          ·
            refine ⟨12267782071417279142036495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8178521380944852761357663 12267782071417279142036495)
            ·
              refine ⟨18401673107125918713054743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12267782071417279142036495 18401673107125918713054743)
              ·
                refine ⟨27602509660688878069582115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18401673107125918713054743 27602509660688878069582115)
                ·
                  refine ⟨41403764491033317104373173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27602509660688878069582115 41403764491033317104373173)
                  ·
                    refine ⟨3881602921034373478534985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41403764491033317104373173 3881602921034373478534985)
                    ·
                      refine ⟨2911202190775780108901239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3881602921034373478534985 2911202190775780108901239)
                      ·
                        rfl

theorem cell23_5669546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_5669546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669546 prefixEnd_5669546 := by exact prefixLift 5669546
  have htrace : WordTrace (prefixWord ++ tailWord_5669546) baseStart_5669546 baseEnd_5669546 := by
    simpa [prefixWord, tailWord_5669546, baseEnd_5669546] using wordTrace_append hprefix tailTrace_5669546
  have hstable : (prefixWord ++ tailWord_5669546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669546).length < 2 ^ (prefixWord ++ tailWord_5669546).sum := by decide
  have hdescent : baseEnd_5669546 < baseStart_5669546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669553 : List Nat := [1, 2, 2, 6, 1, 1, 2, 3, 1, 1, 3]
def baseStart_5669553 : Nat := 118140960795 + 5669553 * 2 ^ 59
def prefixEnd_5669553 : Nat := 4983230072969 + 3 ^ 40 * 5669553 * 2
def baseEnd_5669553 : Nat := 2911205785140361581513707

theorem tailTrace_5669553 : CollatzResearch.WordTrace tailWord_5669553 prefixEnd_5669553 2911205785140361581513707 := by
  unfold tailWord_5669553
  simp only [CollatzResearch.WordTrace]
  refine ⟨206785586029185238408597313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137857057352790158939064875 206785586029185238408597313)
  ·
    refine ⟨155089189521888928806447985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206785586029185238408597313 155089189521888928806447985)
    ·
      refine ⟨116316892141416696604835989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155089189521888928806447985 116316892141416696604835989)
      ·
        refine ⟨5452354319128907653351687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 116316892141416696604835989 5452354319128907653351687)
        ·
          refine ⟨8178531478693361480027531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5452354319128907653351687 8178531478693361480027531)
          ·
            refine ⟨12267797218040042220041297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8178531478693361480027531 12267797218040042220041297)
            ·
              refine ⟨9200847913530031665030973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12267797218040042220041297 9200847913530031665030973)
              ·
                refine ⟨3450317967573761874386615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9200847913530031665030973 3450317967573761874386615)
                ·
                  refine ⟨5175476951360642811579923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3450317967573761874386615 5175476951360642811579923)
                  ·
                    refine ⟨7763215427040964217369885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5175476951360642811579923 7763215427040964217369885)
                    ·
                      refine ⟨2911205785140361581513707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7763215427040964217369885 2911205785140361581513707)
                      ·
                        rfl

theorem cell23_5669553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_5669553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669553 prefixEnd_5669553 := by exact prefixLift 5669553
  have htrace : WordTrace (prefixWord ++ tailWord_5669553) baseStart_5669553 baseEnd_5669553 := by
    simpa [prefixWord, tailWord_5669553, baseEnd_5669553] using wordTrace_append hprefix tailTrace_5669553
  have hstable : (prefixWord ++ tailWord_5669553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669553).length < 2 ^ (prefixWord ++ tailWord_5669553).sum := by decide
  have hdescent : baseEnd_5669553 < baseStart_5669553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669555 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 4]
def baseStart_5669555 : Nat := 118140960795 + 5669555 * 2 ^ 59
def prefixEnd_5669555 : Nat := 4983230072969 + 3 ^ 40 * 5669555 * 2
def baseEnd_5669555 : Nat := 2911206812101670573688697

theorem tailTrace_5669555 : CollatzResearch.WordTrace tailWord_5669555 prefixEnd_5669555 2911206812101670573688697 := by
  unfold tailWord_5669555
  simp only [CollatzResearch.WordTrace]
  refine ⟨206785658975177992750170119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137857105983451995166780079 206785658975177992750170119)
  ·
    refine ⟨310178488462766989125255179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206785658975177992750170119 310178488462766989125255179)
    ·
      refine ⟨465267732694150483687882769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310178488462766989125255179 465267732694150483687882769)
      ·
        refine ⟨348950799520612862765912077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465267732694150483687882769 348950799520612862765912077)
        ·
          refine ⟨130856549820229823537217029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 348950799520612862765912077 130856549820229823537217029)
          ·
            refine ⟨24535603091293091913228193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 130856549820229823537217029 24535603091293091913228193)
            ·
              refine ⟨18401702318469818934921145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24535603091293091913228193 18401702318469818934921145)
              ·
                refine ⟨13801276738852364201190859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18401702318469818934921145 13801276738852364201190859)
                ·
                  refine ⟨20701915108278546301786289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13801276738852364201190859 20701915108278546301786289)
                  ·
                    refine ⟨15526436331208909726339717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20701915108278546301786289 15526436331208909726339717)
                    ·
                      refine ⟨2911206812101670573688697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15526436331208909726339717 2911206812101670573688697)
                      ·
                        rfl

theorem cell23_5669555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_5669555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669555 prefixEnd_5669555 := by exact prefixLift 5669555
  have htrace : WordTrace (prefixWord ++ tailWord_5669555) baseStart_5669555 baseEnd_5669555 := by
    simpa [prefixWord, tailWord_5669555, baseEnd_5669555] using wordTrace_append hprefix tailTrace_5669555
  have hstable : (prefixWord ++ tailWord_5669555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669555).length < 2 ^ (prefixWord ++ tailWord_5669555).sum := by decide
  have hdescent : baseEnd_5669555 < baseStart_5669555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669562 : List Nat := [3, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3]
def baseStart_5669562 : Nat := 118140960795 + 5669562 * 2 ^ 59
def prefixEnd_5669562 : Nat := 4983230072969 + 3 ^ 40 * 5669562 * 2
def baseEnd_5669562 : Nat := 2911210406466252046301165

theorem tailTrace_5669562 : CollatzResearch.WordTrace tailWord_5669562 prefixEnd_5669562 2911210406466252046301165 := by
  unfold tailWord_5669562
  simp only [CollatzResearch.WordTrace]
  refine ⟨51696478571538158236418735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137857276190768421963783293 51696478571538158236418735)
  ·
    refine ⟨77544717857307237354628103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51696478571538158236418735 77544717857307237354628103)
    ·
      refine ⟨116317076785960856031942155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77544717857307237354628103 116317076785960856031942155)
      ·
        refine ⟨174475615178941284047913233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116317076785960856031942155 174475615178941284047913233)
        ·
          refine ⟨130856711384205963035934925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174475615178941284047913233 130856711384205963035934925)
          ·
            refine ⟨49071266769077236138475597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130856711384205963035934925 49071266769077236138475597)
            ·
              refine ⟨18401725038403963551928349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49071266769077236138475597 18401725038403963551928349)
              ·
                refine ⟨6900646889401486331973131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18401725038403963551928349 6900646889401486331973131)
                ·
                  refine ⟨10350970334102229497959697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6900646889401486331973131 10350970334102229497959697)
                  ·
                    refine ⟨7763227750576672123469773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10350970334102229497959697 7763227750576672123469773)
                    ·
                      refine ⟨2911210406466252046301165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7763227750576672123469773 2911210406466252046301165)
                      ·
                        rfl

theorem cell23_5669562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3, 1, 2, 3].length) (baseStart_5669562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669562 prefixEnd_5669562 := by exact prefixLift 5669562
  have htrace : WordTrace (prefixWord ++ tailWord_5669562) baseStart_5669562 baseEnd_5669562 := by
    simpa [prefixWord, tailWord_5669562, baseEnd_5669562] using wordTrace_append hprefix tailTrace_5669562
  have hstable : (prefixWord ++ tailWord_5669562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669562).length < 2 ^ (prefixWord ++ tailWord_5669562).sum := by decide
  have hdescent : baseEnd_5669562 < baseStart_5669562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669576 : List Nat := [2, 1, 3, 1, 2, 3, 2, 4, 1, 2, 2]
def baseStart_5669576 : Nat := 118140960795 + 5669576 * 2 ^ 59
def prefixEnd_5669576 : Nat := 4983230072969 + 3 ^ 40 * 5669576 * 2
def baseEnd_5669576 : Nat := 2911217595195414991526101

theorem tailTrace_5669576 : CollatzResearch.WordTrace tailWord_5669576 prefixEnd_5669576 2911217595195414991526101 := by
  unfold tailWord_5669576
  simp only [CollatzResearch.WordTrace]
  refine ⟨103393212454050956668342291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137857616605401275557789721 103393212454050956668342291)
  ·
    refine ⟨155089818681076435002513437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103393212454050956668342291 155089818681076435002513437)
    ·
      refine ⟨58158682005403663125942539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155089818681076435002513437 58158682005403663125942539)
      ·
        refine ⟨87238023008105494688913809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58158682005403663125942539 87238023008105494688913809)
        ·
          refine ⟨65428517256079121016685357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87238023008105494688913809 65428517256079121016685357)
          ·
            refine ⟨24535693971029670381257009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65428517256079121016685357 24535693971029670381257009)
            ·
              refine ⟨18401770478272252785942757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24535693971029670381257009 18401770478272252785942757)
              ·
                refine ⟨3450331964676047397364267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18401770478272252785942757 3450331964676047397364267)
                ·
                  refine ⟨5175497947014071096046401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3450331964676047397364267 5175497947014071096046401)
                  ·
                    refine ⟨3881623460260553322034801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5175497947014071096046401 3881623460260553322034801)
                    ·
                      refine ⟨2911217595195414991526101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3881623460260553322034801 2911217595195414991526101)
                      ·
                        rfl

theorem cell23_5669576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_5669576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669576 prefixEnd_5669576 := by exact prefixLift 5669576
  have htrace : WordTrace (prefixWord ++ tailWord_5669576) baseStart_5669576 baseEnd_5669576 := by
    simpa [prefixWord, tailWord_5669576, baseEnd_5669576] using wordTrace_append hprefix tailTrace_5669576
  have hstable : (prefixWord ++ tailWord_5669576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669576).length < 2 ^ (prefixWord ++ tailWord_5669576).sum := by decide
  have hdescent : baseEnd_5669576 < baseStart_5669576 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669586 : List Nat := [3, 2, 2, 2, 3, 1, 3, 1, 2, 4]
def baseStart_5669586 : Nat := 118140960795 + 5669586 * 2 ^ 59
def prefixEnd_5669586 : Nat := 4983230072969 + 3 ^ 40 * 5669586 * 2
def baseEnd_5669586 : Nat := 970407576667319984133685

theorem tailTrace_5669586 : CollatzResearch.WordTrace tailWord_5669586 prefixEnd_5669586 970407576667319984133685 := by
  unfold tailWord_5669586
  simp only [CollatzResearch.WordTrace]
  refine ⟨51696697409516421261137153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137857859758710456696365741 51696697409516421261137153)
  ·
    refine ⟨38772523057137315945852865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51696697409516421261137153 38772523057137315945852865)
    ·
      refine ⟨29079392292852986959389649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38772523057137315945852865 29079392292852986959389649)
      ·
        refine ⟨21809544219639740219542237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29079392292852986959389649 21809544219639740219542237)
        ·
          refine ⟨8178579082364902582328339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21809544219639740219542237 8178579082364902582328339)
          ·
            refine ⟨12267868623547353873492509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8178579082364902582328339 12267868623547353873492509)
            ·
              refine ⟨4600450733830257702559691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12267868623547353873492509 4600450733830257702559691)
              ·
                refine ⟨6900676100745386553839537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4600450733830257702559691 6900676100745386553839537)
                ·
                  refine ⟨5175507075559039915379653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6900676100745386553839537 5175507075559039915379653)
                  ·
                    refine ⟨970407576667319984133685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5175507075559039915379653 970407576667319984133685)
                    ·
                      rfl

theorem cell23_5669586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_5669586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669586 prefixEnd_5669586 := by exact prefixLift 5669586
  have htrace : WordTrace (prefixWord ++ tailWord_5669586) baseStart_5669586 baseEnd_5669586 := by
    simpa [prefixWord, tailWord_5669586, baseEnd_5669586] using wordTrace_append hprefix tailTrace_5669586
  have hstable : (prefixWord ++ tailWord_5669586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669586).length < 2 ^ (prefixWord ++ tailWord_5669586).sum := by decide
  have hdescent : baseEnd_5669586 < baseStart_5669586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669592 : List Nat := [2, 1, 2, 2, 3, 2, 3, 1, 1, 3, 3]
def baseStart_5669592 : Nat := 118140960795 + 5669592 * 2 ^ 59
def prefixEnd_5669592 : Nat := 4983230072969 + 3 ^ 40 * 5669592 * 2
def baseEnd_5669592 : Nat := 2911225810885886928926027

theorem tailTrace_5669592 : CollatzResearch.WordTrace tailWord_5669592 prefixEnd_5669592 2911225810885886928926027 := by
  unfold tailWord_5669592
  simp only [CollatzResearch.WordTrace]
  refine ⟨103393504238021974034633515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137858005650695965379511353 103393504238021974034633515)
  ·
    refine ⟨155090256357032961051950273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103393504238021974034633515 155090256357032961051950273)
    ·
      refine ⟨116317692267774720788962705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155090256357032961051950273 116317692267774720788962705)
      ·
        refine ⟨87238269200831040591722029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116317692267774720788962705 87238269200831040591722029)
        ·
          refine ⟨32714350950311640221895761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87238269200831040591722029 32714350950311640221895761)
          ·
            refine ⟨24535763212733730166421821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32714350950311640221895761 24535763212733730166421821)
            ·
              refine ⟨9200911204775148812408183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24535763212733730166421821 9200911204775148812408183)
              ·
                refine ⟨13801366807162723218612275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9200911204775148812408183 13801366807162723218612275)
                ·
                  refine ⟨20702050210744084827918413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13801366807162723218612275 20702050210744084827918413)
                  ·
                    refine ⟨7763268829029031810469405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20702050210744084827918413 7763268829029031810469405)
                    ·
                      refine ⟨2911225810885886928926027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7763268829029031810469405 2911225810885886928926027)
                      ·
                        rfl

theorem cell23_5669592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 1, 1, 3, 3].length) (baseStart_5669592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669592 prefixEnd_5669592 := by exact prefixLift 5669592
  have htrace : WordTrace (prefixWord ++ tailWord_5669592) baseStart_5669592 baseEnd_5669592 := by
    simpa [prefixWord, tailWord_5669592, baseEnd_5669592] using wordTrace_append hprefix tailTrace_5669592
  have hstable : (prefixWord ++ tailWord_5669592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669592).length < 2 ^ (prefixWord ++ tailWord_5669592).sum := by decide
  have hdescent : baseEnd_5669592 < baseStart_5669592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669596 : List Nat := [2, 2, 5, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_5669596 : Nat := 118140960795 + 5669596 * 2 ^ 59
def prefixEnd_5669596 : Nat := 4983230072969 + 3 ^ 40 * 5669596 * 2
def baseEnd_5669596 : Nat := 2911227864808504913276009

theorem tailTrace_5669596 : CollatzResearch.WordTrace tailWord_5669596 prefixEnd_5669596 2911227864808504913276009 := by
  unfold tailWord_5669596
  simp only [CollatzResearch.WordTrace]
  refine ⟨103393577184014728376206321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137858102912019637834941761 103393577184014728376206321)
  ·
    refine ⟨77545182888011046282154741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103393577184014728376206321 77545182888011046282154741)
    ·
      refine ⟨7269860895751035588952007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 77545182888011046282154741 7269860895751035588952007)
      ·
        refine ⟨10904791343626553383428011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7269860895751035588952007 10904791343626553383428011)
        ·
          refine ⟨16357187015439830075142017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10904791343626553383428011 16357187015439830075142017)
          ·
            refine ⟨12267890261579872556356513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16357187015439830075142017 12267890261579872556356513)
            ·
              refine ⟨9200917696184904417267385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12267890261579872556356513 9200917696184904417267385)
              ·
                refine ⟨6900688272138678312950539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9200917696184904417267385 6900688272138678312950539)
                ·
                  refine ⟨10351032408208017469425809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6900688272138678312950539 10351032408208017469425809)
                  ·
                    refine ⟨7763274306156013102069357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10351032408208017469425809 7763274306156013102069357)
                    ·
                      refine ⟨2911227864808504913276009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7763274306156013102069357 2911227864808504913276009)
                      ·
                        rfl

theorem cell23_5669596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_5669596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669596 prefixEnd_5669596 := by exact prefixLift 5669596
  have htrace : WordTrace (prefixWord ++ tailWord_5669596) baseStart_5669596 baseEnd_5669596 := by
    simpa [prefixWord, tailWord_5669596, baseEnd_5669596] using wordTrace_append hprefix tailTrace_5669596
  have hstable : (prefixWord ++ tailWord_5669596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669596).length < 2 ^ (prefixWord ++ tailWord_5669596).sum := by decide
  have hdescent : baseEnd_5669596 < baseStart_5669596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669605 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 2, 2, 5]
def baseStart_5669605 : Nat := 118140960795 + 5669605 * 2 ^ 59
def prefixEnd_5669605 : Nat := 4983230072969 + 3 ^ 40 * 5669605 * 2
def baseEnd_5669605 : Nat := 2911232486134395378063467

theorem tailTrace_5669605 : CollatzResearch.WordTrace tailWord_5669605 prefixEnd_5669605 2911232486134395378063467 := by
  unfold tailWord_5669605
  simp only [CollatzResearch.WordTrace]
  refine ⟨206787482624996851289490269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137858321749997900859660179 206787482624996851289490269)
  ·
    refine ⟨77545305984373819233558851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206787482624996851289490269 77545305984373819233558851)
    ·
      refine ⟨116317958976560728850338277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77545305984373819233558851 116317958976560728850338277)
      ·
        refine ⟨21809617308105136659438427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116317958976560728850338277 21809617308105136659438427)
        ·
          refine ⟨32714425962157704989157641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21809617308105136659438427 32714425962157704989157641)
          ·
            refine ⟨24535819471618278741868231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32714425962157704989157641 24535819471618278741868231)
            ·
              refine ⟨36803729207427418112802347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24535819471618278741868231 36803729207427418112802347)
              ·
                refine ⟨55205593811141127169203521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36803729207427418112802347 55205593811141127169203521)
                ·
                  refine ⟨41404195358355845376902641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55205593811141127169203521 41404195358355845376902641)
                  ·
                    refine ⟨31053146518766884032676981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41404195358355845376902641 31053146518766884032676981)
                    ·
                      refine ⟨2911232486134395378063467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31053146518766884032676981 2911232486134395378063467)
                      ·
                        rfl

theorem cell23_5669605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_5669605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669605 prefixEnd_5669605 := by exact prefixLift 5669605
  have htrace : WordTrace (prefixWord ++ tailWord_5669605) baseStart_5669605 baseEnd_5669605 := by
    simpa [prefixWord, tailWord_5669605, baseEnd_5669605] using wordTrace_append hprefix tailTrace_5669605
  have hstable : (prefixWord ++ tailWord_5669605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669605).length < 2 ^ (prefixWord ++ tailWord_5669605).sum := by decide
  have hdescent : baseEnd_5669605 < baseStart_5669605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669635 : List Nat := [1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 3]
def baseStart_5669635 : Nat := 118140960795 + 5669635 * 2 ^ 59
def prefixEnd_5669635 : Nat := 4983230072969 + 3 ^ 40 * 5669635 * 2
def baseEnd_5669635 : Nat := 2911247890554030260688329

theorem tailTrace_5669635 : CollatzResearch.WordTrace tailWord_5669635 prefixEnd_5669635 2911247890554030260688329 := by
  unfold tailWord_5669635
  simp only [CollatzResearch.WordTrace]
  refine ⟨206788576814888166413082359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137859051209925444275388239 206788576814888166413082359)
  ·
    refine ⟨310182865222332249619623539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206788576814888166413082359 310182865222332249619623539)
    ·
      refine ⟨465274297833498374429435309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310182865222332249619623539 465274297833498374429435309)
      ·
        refine ⟨174477861687561890411038241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 465274297833498374429435309 174477861687561890411038241)
        ·
          refine ⟨130858396265671417808278681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174477861687561890411038241 130858396265671417808278681)
          ·
            refine ⟨98143797199253563356209011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130858396265671417808278681 98143797199253563356209011)
            ·
              refine ⟨147215695798880345034313517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98143797199253563356209011 147215695798880345034313517)
              ·
                refine ⟨55205885924580129387867569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147215695798880345034313517 55205885924580129387867569)
                ·
                  refine ⟨41404414443435097040900677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55205885924580129387867569 41404414443435097040900677)
                  ·
                    refine ⟨7763327708144080695168877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41404414443435097040900677 7763327708144080695168877)
                    ·
                      refine ⟨2911247890554030260688329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7763327708144080695168877 2911247890554030260688329)
                      ·
                        rfl

theorem cell23_5669635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_5669635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669635 prefixEnd_5669635 := by exact prefixLift 5669635
  have htrace : WordTrace (prefixWord ++ tailWord_5669635) baseStart_5669635 baseEnd_5669635 := by
    simpa [prefixWord, tailWord_5669635, baseEnd_5669635] using wordTrace_append hprefix tailTrace_5669635
  have hstable : (prefixWord ++ tailWord_5669635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669635).length < 2 ^ (prefixWord ++ tailWord_5669635).sum := by decide
  have hdescent : baseEnd_5669635 < baseStart_5669635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669682 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3]
def baseStart_5669682 : Nat := 118140960795 + 5669682 * 2 ^ 59
def prefixEnd_5669682 : Nat := 4983230072969 + 3 ^ 40 * 5669682 * 2
def baseEnd_5669682 : Nat := 2911272024144791576800613

theorem tailTrace_5669682 : CollatzResearch.WordTrace tailWord_5669682 prefixEnd_5669682 2911272024144791576800613 := by
  unfold tailWord_5669682
  simp only [CollatzResearch.WordTrace]
  refine ⟨51697572761429473360010825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137860194030478595626695533 51697572761429473360010825)
  ·
    refine ⟨38773179571072105020008119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51697572761429473360010825 38773179571072105020008119)
    ·
      refine ⟨58159769356608157530012179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38773179571072105020008119 58159769356608157530012179)
      ·
        refine ⟨87239654034912236295018269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58159769356608157530012179 87239654034912236295018269)
        ·
          refine ⟨32714870263092088610631851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87239654034912236295018269 32714870263092088610631851)
          ·
            refine ⟨49072305394638132915947777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32714870263092088610631851 49072305394638132915947777)
            ·
              refine ⟨36804229045978599686960833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49072305394638132915947777 36804229045978599686960833)
              ·
                refine ⟨27603171784483949765220625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36804229045978599686960833 27603171784483949765220625)
                ·
                  refine ⟨20702378838362962323915469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27603171784483949765220625 20702378838362962323915469)
                  ·
                    refine ⟨7763392064386110871468301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20702378838362962323915469 7763392064386110871468301)
                    ·
                      refine ⟨2911272024144791576800613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7763392064386110871468301 2911272024144791576800613)
                      ·
                        rfl

theorem cell23_5669682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_5669682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669682 prefixEnd_5669682 := by exact prefixLift 5669682
  have htrace : WordTrace (prefixWord ++ tailWord_5669682) baseStart_5669682 baseEnd_5669682 := by
    simpa [prefixWord, tailWord_5669682, baseEnd_5669682] using wordTrace_append hprefix tailTrace_5669682
  have hstable : (prefixWord ++ tailWord_5669682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669682).length < 2 ^ (prefixWord ++ tailWord_5669682).sum := by decide
  have hdescent : baseEnd_5669682 < baseStart_5669682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669719 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 2, 5]
def baseStart_5669719 : Nat := 118140960795 + 5669719 * 2 ^ 59
def prefixEnd_5669719 : Nat := 4983230072969 + 3 ^ 40 * 5669719 * 2
def baseEnd_5669719 : Nat := 970430340976335977345981

theorem tailTrace_5669719 : CollatzResearch.WordTrace tailWord_5669719 prefixEnd_5669719 970430340976335977345981 := by
  unfold tailWord_5669719
  simp only [CollatzResearch.WordTrace]
  refine ⟨206791640546583848759140211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137861093697722565839426807 206791640546583848759140211)
  ·
    refine ⟨310187460819875773138710317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206791640546583848759140211 310187460819875773138710317)
    ·
      refine ⟨116320297807453414927016369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310187460819875773138710317 116320297807453414927016369)
      ·
        refine ⟨87240223355590061195262277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116320297807453414927016369 87240223355590061195262277)
        ·
          refine ⟨16357541879173136474111677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87240223355590061195262277 16357541879173136474111677)
          ·
            refine ⟨6134078204689926177791879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16357541879173136474111677 6134078204689926177791879)
            ·
              refine ⟨9201117307034889266687819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6134078204689926177791879 9201117307034889266687819)
              ·
                refine ⟨13801675960552333900031729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9201117307034889266687819 13801675960552333900031729)
                ·
                  refine ⟨10351256970414250425023797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13801675960552333900031729 10351256970414250425023797)
                  ·
                    refine ⟨970430340976335977345981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10351256970414250425023797 970430340976335977345981)
                    ·
                      rfl

theorem cell23_5669719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_5669719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669719 prefixEnd_5669719 := by exact prefixLift 5669719
  have htrace : WordTrace (prefixWord ++ tailWord_5669719) baseStart_5669719 baseEnd_5669719 := by
    simpa [prefixWord, tailWord_5669719, baseEnd_5669719] using wordTrace_append hprefix tailTrace_5669719
  have hstable : (prefixWord ++ tailWord_5669719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669719).length < 2 ^ (prefixWord ++ tailWord_5669719).sum := by decide
  have hdescent : baseEnd_5669719 < baseStart_5669719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669722 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4]
def baseStart_5669722 : Nat := 118140960795 + 5669722 * 2 ^ 59
def prefixEnd_5669722 : Nat := 4983230072969 + 3 ^ 40 * 5669722 * 2
def baseEnd_5669722 : Nat := 2911292563370971420300429

theorem tailTrace_5669722 : CollatzResearch.WordTrace tailWord_5669722 prefixEnd_5669722 2911292563370971420300429 := by
  unfold tailWord_5669722
  simp only [CollatzResearch.WordTrace]
  refine ⟨51697937491393245067874855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137861166643715320180999613 51697937491393245067874855)
  ·
    refine ⟨77546906237089867601812283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51697937491393245067874855 77546906237089867601812283)
    ·
      refine ⟨116320359355634801402718425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77546906237089867601812283 116320359355634801402718425)
      ·
        refine ⟨87240269516726101052038819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116320359355634801402718425 87240269516726101052038819)
        ·
          refine ⟨130860404275089151578058229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87240269516726101052038819 130860404275089151578058229)
          ·
            refine ⟨12268162900789607960442959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 130860404275089151578058229 12268162900789607960442959)
            ·
              refine ⟨18402244351184411940664439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12268162900789607960442959 18402244351184411940664439)
              ·
                refine ⟨27603366526776617910996659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18402244351184411940664439 27603366526776617910996659)
                ·
                  refine ⟨41405049790164926866494989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27603366526776617910996659 41405049790164926866494989)
                  ·
                    refine ⟨15526893671311847574935621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41405049790164926866494989 15526893671311847574935621)
                    ·
                      refine ⟨2911292563370971420300429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15526893671311847574935621 2911292563370971420300429)
                      ·
                        rfl

theorem cell23_5669722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_5669722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669722 prefixEnd_5669722 := by exact prefixLift 5669722
  have htrace : WordTrace (prefixWord ++ tailWord_5669722) baseStart_5669722 baseEnd_5669722 := by
    simpa [prefixWord, tailWord_5669722, baseEnd_5669722] using wordTrace_append hprefix tailTrace_5669722
  have hstable : (prefixWord ++ tailWord_5669722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669722).length < 2 ^ (prefixWord ++ tailWord_5669722).sum := by decide
  have hdescent : baseEnd_5669722 < baseStart_5669722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669749 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 3, 4]
def baseStart_5669749 : Nat := 118140960795 + 5669749 * 2 ^ 59
def prefixEnd_5669749 : Nat := 4983230072969 + 3 ^ 40 * 5669749 * 2
def baseEnd_5669749 : Nat := 970435475782880938220935

theorem tailTrace_5669749 : CollatzResearch.WordTrace tailWord_5669749 prefixEnd_5669749 970435475782880938220935 := by
  unfold tailWord_5669749
  simp only [CollatzResearch.WordTrace]
  refine ⟨206792734736475163882732301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137861823157650109255154867 206792734736475163882732301)
  ·
    refine ⟨77547275526178186456024613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206792734736475163882732301 77547275526178186456024613)
    ·
      refine ⟨14540114161158409960504615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77547275526178186456024613 14540114161158409960504615)
      ·
        refine ⟨21810171241737614940756923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14540114161158409960504615 21810171241737614940756923)
        ·
          refine ⟨32715256862606422411135385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21810171241737614940756923 32715256862606422411135385)
          ·
            refine ⟨24536442646954816808351539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32715256862606422411135385 24536442646954816808351539)
            ·
              refine ⟨36804663970432225212527309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24536442646954816808351539 36804663970432225212527309)
              ·
                refine ⟨13801748988912084454697741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36804663970432225212527309 13801748988912084454697741)
                ·
                  refine ⟨5175655870842031670511653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13801748988912084454697741 5175655870842031670511653)
                  ·
                    refine ⟨970435475782880938220935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5175655870842031670511653 970435475782880938220935)
                    ·
                      rfl

theorem cell23_5669749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_5669749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669749 prefixEnd_5669749 := by exact prefixLift 5669749
  have htrace : WordTrace (prefixWord ++ tailWord_5669749) baseStart_5669749 baseEnd_5669749 := by
    simpa [prefixWord, tailWord_5669749, baseEnd_5669749] using wordTrace_append hprefix tailTrace_5669749
  have hstable : (prefixWord ++ tailWord_5669749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669749).length < 2 ^ (prefixWord ++ tailWord_5669749).sum := by decide
  have hdescent : baseEnd_5669749 < baseStart_5669749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669849 : List Nat := [1, 2, 1, 2, 5, 1, 3, 1, 1, 1, 5]
def baseStart_5669849 : Nat := 118140960795 + 5669849 * 2 ^ 59
def prefixEnd_5669849 : Nat := 4983230072969 + 3 ^ 40 * 5669849 * 2
def baseEnd_5669849 : Nat := 2911357775414092423412345

theorem tailTrace_5669849 : CollatzResearch.WordTrace tailWord_5669849 prefixEnd_5669849 2911357775414092423412345 := by
  unfold tailWord_5669849
  simp only [CollatzResearch.WordTrace]
  refine ⟨206796382036112880961372601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137864254690741920640915067 206796382036112880961372601)
  ·
    refine ⟨155097286527084660721029451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206796382036112880961372601 155097286527084660721029451)
    ·
      refine ⟨232645929790626991081544177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155097286527084660721029451 232645929790626991081544177)
      ·
        refine ⟨174484447342970243311158133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232645929790626991081544177 174484447342970243311158133)
        ·
          refine ⟨16357916938403460310421075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174484447342970243311158133 16357916938403460310421075)
          ·
            refine ⟨24536875407605190465631613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16357916938403460310421075 24536875407605190465631613)
            ·
              refine ⟨9201328277851946424611855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24536875407605190465631613 9201328277851946424611855)
              ·
                refine ⟨13801992416777919636917783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9201328277851946424611855 13801992416777919636917783)
                ·
                  refine ⟨20702988625166879455376675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13801992416777919636917783 20702988625166879455376675)
                  ·
                    refine ⟨31054482937750319183065013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20702988625166879455376675 31054482937750319183065013)
                    ·
                      refine ⟨2911357775414092423412345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31054482937750319183065013 2911357775414092423412345)
                      ·
                        rfl

theorem cell23_5669849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_5669849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669849 prefixEnd_5669849 := by exact prefixLift 5669849
  have htrace : WordTrace (prefixWord ++ tailWord_5669849) baseStart_5669849 baseEnd_5669849 := by
    simpa [prefixWord, tailWord_5669849, baseEnd_5669849] using wordTrace_append hprefix tailTrace_5669849
  have hstable : (prefixWord ++ tailWord_5669849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669849).length < 2 ^ (prefixWord ++ tailWord_5669849).sum := by decide
  have hdescent : baseEnd_5669849 < baseStart_5669849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669930 : List Nat := [3, 1, 4, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_5669930 : Nat := 118140960795 + 5669930 * 2 ^ 59
def prefixEnd_5669930 : Nat := 4983230072969 + 3 ^ 40 * 5669930 * 2
def baseEnd_5669930 : Nat := 2911399367347106606499473

theorem tailTrace_5669930 : CollatzResearch.WordTrace tailWord_5669930 prefixEnd_5669930 2911399367347106606499473 := by
  unfold tailWord_5669930
  simp only [CollatzResearch.WordTrace]
  refine ⟨51699834087204857948767811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137866224232546287863380829 51699834087204857948767811)
  ·
    refine ⟨77549751130807286923151717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51699834087204857948767811 77549751130807286923151717)
    ·
      refine ⟨14540578337026366298090947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77549751130807286923151717 14540578337026366298090947)
      ·
        refine ⟨21810867505539549447136421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14540578337026366298090947 21810867505539549447136421)
        ·
          refine ⟨4089537657288665521338079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21810867505539549447136421 4089537657288665521338079)
          ·
            refine ⟨6134306485932998282007119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4089537657288665521338079 6134306485932998282007119)
            ·
              refine ⟨9201459728899497423010679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6134306485932998282007119 9201459728899497423010679)
              ·
                refine ⟨13802189593349246134516019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9201459728899497423010679 13802189593349246134516019)
                ·
                  refine ⟨20703284390023869201774029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13802189593349246134516019 20703284390023869201774029)
                  ·
                    refine ⟨7763731646258950950665261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20703284390023869201774029 7763731646258950950665261)
                    ·
                      refine ⟨2911399367347106606499473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7763731646258950950665261 2911399367347106606499473)
                      ·
                        rfl

theorem cell23_5669930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_5669930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669930 prefixEnd_5669930 := by exact prefixLift 5669930
  have htrace : WordTrace (prefixWord ++ tailWord_5669930) baseStart_5669930 baseEnd_5669930 := by
    simpa [prefixWord, tailWord_5669930, baseEnd_5669930] using wordTrace_append hprefix tailTrace_5669930
  have hstable : (prefixWord ++ tailWord_5669930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669930).length < 2 ^ (prefixWord ++ tailWord_5669930).sum := by decide
  have hdescent : baseEnd_5669930 < baseStart_5669930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669940 : List Nat := [2, 5, 1, 2, 1, 1, 1, 4, 1, 3, 2]
def baseStart_5669940 : Nat := 118140960795 + 5669940 * 2 ^ 59
def prefixEnd_5669940 : Nat := 4983230072969 + 3 ^ 40 * 5669940 * 2
def baseEnd_5669940 : Nat := 2911404502153651567374427

theorem tailTrace_5669940 : CollatzResearch.WordTrace tailWord_5669940 prefixEnd_5669940 2911404502153651567374427 := by
  unfold tailWord_5669940
  simp only [CollatzResearch.WordTrace]
  refine ⟨103399850539391601751467637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137866467385855469001956849 103399850539391601751467637)
  ·
    refine ⟨9693735988067962664200091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103399850539391601751467637 9693735988067962664200091)
    ·
      refine ⟨14540603982101943996300137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9693735988067962664200091 14540603982101943996300137)
      ·
        refine ⟨10905452986576457997225103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14540603982101943996300137 10905452986576457997225103)
        ·
          refine ⟨16358179479864686995837655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10905452986576457997225103 16358179479864686995837655)
          ·
            refine ⟨24537269219797030493756483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16358179479864686995837655 24537269219797030493756483)
            ·
              refine ⟨36805903829695545740634725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24537269219797030493756483 36805903829695545740634725)
              ·
                refine ⟨6901106968067914826369011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36805903829695545740634725 6901106968067914826369011)
                ·
                  refine ⟨10351660452101872239553517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6901106968067914826369011 10351660452101872239553517)
                  ·
                    refine ⟨3881872669538202089832569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10351660452101872239553517 3881872669538202089832569)
                    ·
                      refine ⟨2911404502153651567374427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3881872669538202089832569 2911404502153651567374427)
                      ·
                        rfl

theorem cell23_5669940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_5669940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669940 prefixEnd_5669940 := by exact prefixLift 5669940
  have htrace : WordTrace (prefixWord ++ tailWord_5669940) baseStart_5669940 baseEnd_5669940 := by
    simpa [prefixWord, tailWord_5669940, baseEnd_5669940] using wordTrace_append hprefix tailTrace_5669940
  have hstable : (prefixWord ++ tailWord_5669940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669940).length < 2 ^ (prefixWord ++ tailWord_5669940).sum := by decide
  have hdescent : baseEnd_5669940 < baseStart_5669940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669969 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 4, 3, 3]
def baseStart_5669969 : Nat := 118140960795 + 5669969 * 2 ^ 59
def prefixEnd_5669969 : Nat := 4983230072969 + 3 ^ 40 * 5669969 * 2
def baseEnd_5669969 : Nat := 2911419393092631953911793

theorem tailTrace_5669969 : CollatzResearch.WordTrace tailWord_5669969 prefixEnd_5669969 2911419393092631953911793 := by
  unfold tailWord_5669969
  simp only [CollatzResearch.WordTrace]
  refine ⟨206800758795678141455740961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137867172530452094303827307 206800758795678141455740961)
  ·
    refine ⟨155100569096758606091805721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206800758795678141455740961 155100569096758606091805721)
    ·
      refine ⟨116325426822568954568854291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155100569096758606091805721 116325426822568954568854291)
      ·
        refine ⟨174488140233853431853281437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116325426822568954568854291 174488140233853431853281437)
        ·
          refine ⟨65433052587695036944980539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174488140233853431853281437 65433052587695036944980539)
          ·
            refine ⟨98149578881542555417470809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65433052587695036944980539 98149578881542555417470809)
            ·
              refine ⟨73612184161156916563103107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98149578881542555417470809 73612184161156916563103107)
              ·
                refine ⟨110418276241735374844654661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73612184161156916563103107 110418276241735374844654661)
                ·
                  refine ⟨20703426795325382783372749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110418276241735374844654661 20703426795325382783372749)
                  ·
                    refine ⟨7763785048247018543764781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20703426795325382783372749 7763785048247018543764781)
                    ·
                      refine ⟨2911419393092631953911793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7763785048247018543764781 2911419393092631953911793)
                      ·
                        rfl

theorem cell23_5669969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_5669969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669969 prefixEnd_5669969 := by exact prefixLift 5669969
  have htrace : WordTrace (prefixWord ++ tailWord_5669969) baseStart_5669969 baseEnd_5669969 := by
    simpa [prefixWord, tailWord_5669969, baseEnd_5669969] using wordTrace_append hprefix tailTrace_5669969
  have hstable : (prefixWord ++ tailWord_5669969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669969).length < 2 ^ (prefixWord ++ tailWord_5669969).sum := by decide
  have hdescent : baseEnd_5669969 < baseStart_5669969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5669989 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 4, 5]
def baseStart_5669989 : Nat := 118140960795 + 5669989 * 2 ^ 59
def prefixEnd_5669989 : Nat := 4983230072969 + 3 ^ 40 * 5669989 * 2
def baseEnd_5669989 : Nat := 970476554235240625220567

theorem tailTrace_5669989 : CollatzResearch.WordTrace tailWord_5669989 prefixEnd_5669989 970476554235240625220567 := by
  unfold tailWord_5669989
  simp only [CollatzResearch.WordTrace]
  refine ⟨206801488255605684871469021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137867658837070456580979347 206801488255605684871469021)
  ·
    refine ⟨77550558095852131826800883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206801488255605684871469021 77550558095852131826800883)
    ·
      refine ⟨116325837143778197740201325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77550558095852131826800883 116325837143778197740201325)
      ·
        refine ⟨43622188928916824152575497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116325837143778197740201325 43622188928916824152575497)
        ·
          refine ⟨32716641696687618114431623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43622188928916824152575497 32716641696687618114431623)
          ·
            refine ⟨49074962545031427171647435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32716641696687618114431623 49074962545031427171647435)
            ·
              refine ⟨73612443817547140757471153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49074962545031427171647435 73612443817547140757471153)
              ·
                refine ⟨55209332863160355568103365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73612443817547140757471153 55209332863160355568103365)
                ·
                  refine ⟨10351749911842566669019381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55209332863160355568103365 10351749911842566669019381)
                  ·
                    refine ⟨970476554235240625220567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10351749911842566669019381 970476554235240625220567)
                    ·
                      rfl

theorem cell23_5669989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_5669989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5669989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5669989 prefixEnd_5669989 := by exact prefixLift 5669989
  have htrace : WordTrace (prefixWord ++ tailWord_5669989) baseStart_5669989 baseEnd_5669989 := by
    simpa [prefixWord, tailWord_5669989, baseEnd_5669989] using wordTrace_append hprefix tailTrace_5669989
  have hstable : (prefixWord ++ tailWord_5669989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5669989).length < 2 ^ (prefixWord ++ tailWord_5669989).sum := by decide
  have hdescent : baseEnd_5669989 < baseStart_5669989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5669989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670026 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_5670026 : Nat := 118140960795 + 5670026 * 2 ^ 59
def prefixEnd_5670026 : Nat := 4983230072969 + 3 ^ 40 * 5670026 * 2
def baseEnd_5670026 : Nat := 2911448661489938230899031

theorem tailTrace_5670026 : CollatzResearch.WordTrace tailWord_5670026 prefixEnd_5670026 2911448661489938230899031 := by
  unfold tailWord_5670026
  simp only [CollatzResearch.WordTrace]
  refine ⟨51700709439117910047641483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137868558504314426793710621 51700709439117910047641483)
  ·
    refine ⟨77551064158676865071462225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51700709439117910047641483 77551064158676865071462225)
    ·
      refine ⟨58163298119007648803596669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77551064158676865071462225 58163298119007648803596669)
      ·
        refine ⟨21811236794627868301348751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58163298119007648803596669 21811236794627868301348751)
        ·
          refine ⟨32716855191941802452023127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21811236794627868301348751 32716855191941802452023127)
          ·
            refine ⟨49075282787912703678034691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32716855191941802452023127 49075282787912703678034691)
            ·
              refine ⟨73612924181869055517052037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49075282787912703678034691 73612924181869055517052037)
              ·
                refine ⟨13802423284100447909447257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73612924181869055517052037 13802423284100447909447257)
                ·
                  refine ⟨10351817463075335932085443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13802423284100447909447257 10351817463075335932085443)
                  ·
                    refine ⟨15527726194613003898128165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10351817463075335932085443 15527726194613003898128165)
                    ·
                      refine ⟨2911448661489938230899031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15527726194613003898128165 2911448661489938230899031)
                      ·
                        rfl

theorem cell23_5670026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_5670026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670026 prefixEnd_5670026 := by exact prefixLift 5670026
  have htrace : WordTrace (prefixWord ++ tailWord_5670026) baseStart_5670026 baseEnd_5670026 := by
    simpa [prefixWord, tailWord_5670026, baseEnd_5670026] using wordTrace_append hprefix tailTrace_5670026
  have hstable : (prefixWord ++ tailWord_5670026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670026).length < 2 ^ (prefixWord ++ tailWord_5670026).sum := by decide
  have hdescent : baseEnd_5670026 < baseStart_5670026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670113 : List Nat := [1, 2, 3, 1, 3, 3, 2, 2, 1, 5]
def baseStart_5670113 : Nat := 118140960795 + 5670113 * 2 ^ 59
def prefixEnd_5670113 : Nat := 4983230072969 + 3 ^ 40 * 5670113 * 2
def baseEnd_5670113 : Nat := 970497778102293130170377

theorem tailTrace_5670113 : CollatzResearch.WordTrace tailWord_5670113 prefixEnd_5670113 970497778102293130170377 := by
  unfold tailWord_5670113
  simp only [CollatzResearch.WordTrace]
  refine ⟨206806010907156454048982993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137870673938104302699321995 206806010907156454048982993)
  ·
    refine ⟨155104508180367340536737245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206806010907156454048982993 155104508180367340536737245)
    ·
      refine ⟨58164190567637752701276467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155104508180367340536737245 58164190567637752701276467)
      ·
        refine ⟨87246285851456629051914701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58164190567637752701276467 87246285851456629051914701)
        ·
          refine ⟨32717357194296235894468013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87246285851456629051914701 32717357194296235894468013)
          ·
            refine ⟨12269008947861088460425505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32717357194296235894468013 12269008947861088460425505)
            ·
              refine ⟨9201756710895816345319129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12269008947861088460425505 9201756710895816345319129)
              ·
                refine ⟨6901317533171862258989347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9201756710895816345319129 6901317533171862258989347)
                ·
                  refine ⟨10351976299757793388484021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6901317533171862258989347 10351976299757793388484021)
                  ·
                    refine ⟨970497778102293130170377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10351976299757793388484021 970497778102293130170377)
                    ·
                      rfl

theorem cell23_5670113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_5670113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670113 prefixEnd_5670113 := by exact prefixLift 5670113
  have htrace : WordTrace (prefixWord ++ tailWord_5670113) baseStart_5670113 baseEnd_5670113 := by
    simpa [prefixWord, tailWord_5670113, baseEnd_5670113] using wordTrace_append hprefix tailTrace_5670113
  have hstable : (prefixWord ++ tailWord_5670113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670113).length < 2 ^ (prefixWord ++ tailWord_5670113).sum := by decide
  have hdescent : baseEnd_5670113 < baseStart_5670113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670116 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_5670116 : Nat := 118140960795 + 5670116 * 2 ^ 59
def prefixEnd_5670116 : Nat := 4983230072969 + 3 ^ 40 * 5670116 * 2
def baseEnd_5670116 : Nat := 2911494874748842878773617

theorem tailTrace_5670116 : CollatzResearch.WordTrace tailWord_5670116 prefixEnd_5670116 2911494874748842878773617 := by
  unfold tailWord_5670116
  simp only [CollatzResearch.WordTrace]
  refine ⟨103403060163072792780671101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137870746884097057040894801 103403060163072792780671101)
  ·
    refine ⟨38776147561152297292751663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103403060163072792780671101 38776147561152297292751663)
    ·
      refine ⟨58164221341728445939127495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38776147561152297292751663 58164221341728445939127495)
      ·
        refine ⟨87246332012592668908691243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58164221341728445939127495 87246332012592668908691243)
        ·
          refine ⟨130869498018889003363036865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87246332012592668908691243 130869498018889003363036865)
          ·
            refine ⟨98152123514166752522277649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130869498018889003363036865 98152123514166752522277649)
            ·
              refine ⟨73614092635625064391708237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98152123514166752522277649 73614092635625064391708237)
              ·
                refine ⟨27605284738359399146890589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73614092635625064391708237 27605284738359399146890589)
                ·
                  refine ⟨10351981776884774680083971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27605284738359399146890589 10351981776884774680083971)
                  ·
                    refine ⟨15527972665327162020125957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10351981776884774680083971 15527972665327162020125957)
                    ·
                      refine ⟨2911494874748842878773617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15527972665327162020125957 2911494874748842878773617)
                      ·
                        rfl

theorem cell23_5670116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_5670116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670116 prefixEnd_5670116 := by exact prefixLift 5670116
  have htrace : WordTrace (prefixWord ++ tailWord_5670116) baseStart_5670116 baseEnd_5670116 := by
    simpa [prefixWord, tailWord_5670116, baseEnd_5670116] using wordTrace_append hprefix tailTrace_5670116
  have hstable : (prefixWord ++ tailWord_5670116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670116).length < 2 ^ (prefixWord ++ tailWord_5670116).sum := by decide
  have hdescent : baseEnd_5670116 < baseStart_5670116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670126 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 1, 6]
def baseStart_5670126 : Nat := 118140960795 + 5670126 * 2 ^ 59
def prefixEnd_5670126 : Nat := 4983230072969 + 3 ^ 40 * 5670126 * 2
def baseEnd_5670126 : Nat := 970500003185129279882857

theorem tailTrace_5670126 : CollatzResearch.WordTrace tailWord_5670126 prefixEnd_5670126 970500003185129279882857 := by
  unfold tailWord_5670126
  simp only [CollatzResearch.WordTrace]
  refine ⟨25850810632013669658650779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137870990037406238179470821 25850810632013669658650779)
  ·
    refine ⟨38776215948020504487976169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25850810632013669658650779 38776215948020504487976169)
    ·
      refine ⟨29082161961015378365982127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38776215948020504487976169 29082161961015378365982127)
      ·
        refine ⟨43623242941523067548973191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29082161961015378365982127 43623242941523067548973191)
        ·
          refine ⟨65434864412284601323459787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43623242941523067548973191 65434864412284601323459787)
          ·
            refine ⟨98152296618426901985189681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65434864412284601323459787 98152296618426901985189681)
            ·
              refine ⟨73614222463820176488892261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98152296618426901985189681 73614222463820176488892261)
              ·
                refine ⟨13802666711966283091667299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73614222463820176488892261 13802666711966283091667299)
                ·
                  refine ⟨20704000067949424637500949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13802666711966283091667299 20704000067949424637500949)
                  ·
                    refine ⟨970500003185129279882857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20704000067949424637500949 970500003185129279882857)
                    ·
                      rfl

theorem cell23_5670126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_5670126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670126 prefixEnd_5670126 := by exact prefixLift 5670126
  have htrace : WordTrace (prefixWord ++ tailWord_5670126) baseStart_5670126 baseEnd_5670126 := by
    simpa [prefixWord, tailWord_5670126, baseEnd_5670126] using wordTrace_append hprefix tailTrace_5670126
  have hstable : (prefixWord ++ tailWord_5670126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670126).length < 2 ^ (prefixWord ++ tailWord_5670126).sum := by decide
  have hdescent : baseEnd_5670126 < baseStart_5670126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670136 : List Nat := [2, 1, 2, 1, 1, 2, 1, 1, 7, 2, 3]
def baseStart_5670136 : Nat := 118140960795 + 5670136 * 2 ^ 59
def prefixEnd_5670136 : Nat := 4983230072969 + 3 ^ 40 * 5670136 * 2
def baseEnd_5670136 : Nat := 2911505144361932800523525

theorem tailTrace_5670136 : CollatzResearch.WordTrace tailWord_5670136 prefixEnd_5670136 2911505144361932800523525 := by
  unfold tailWord_5670136
  simp only [CollatzResearch.WordTrace]
  refine ⟨103403424893036564488535131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137871233190715419318046841 103403424893036564488535131)
  ·
    refine ⟨155105137339554846732802697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103403424893036564488535131 155105137339554846732802697)
    ·
      refine ⟨116328853004666135049602023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155105137339554846732802697 116328853004666135049602023)
      ·
        refine ⟨174493279506999202574403035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116328853004666135049602023 174493279506999202574403035)
        ·
          refine ⟨261739919260498803861604553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174493279506999202574403035 261739919260498803861604553)
          ·
            refine ⟨196304939445374102896203415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261739919260498803861604553 196304939445374102896203415)
            ·
              refine ⟨294457409168061154344305123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196304939445374102896203415 294457409168061154344305123)
              ·
                refine ⟨441686113752091731516457685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294457409168061154344305123 441686113752091731516457685)
                ·
                  refine ⟨10352018291064649957416977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 441686113752091731516457685 10352018291064649957416977)
                  ·
                    refine ⟨7764013718298487468062733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10352018291064649957416977 7764013718298487468062733)
                    ·
                      refine ⟨2911505144361932800523525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7764013718298487468062733 2911505144361932800523525)
                      ·
                        rfl

theorem cell23_5670136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_5670136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670136 prefixEnd_5670136 := by exact prefixLift 5670136
  have htrace : WordTrace (prefixWord ++ tailWord_5670136) baseStart_5670136 baseEnd_5670136 := by
    simpa [prefixWord, tailWord_5670136, baseEnd_5670136] using wordTrace_append hprefix tailTrace_5670136
  have hstable : (prefixWord ++ tailWord_5670136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670136).length < 2 ^ (prefixWord ++ tailWord_5670136).sum := by decide
  have hdescent : baseEnd_5670136 < baseStart_5670136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670156 : List Nat := [2, 2, 1, 2, 2, 4, 2, 8]
def baseStart_5670156 : Nat := 118140960795 + 5670156 * 2 ^ 59
def prefixEnd_5670156 : Nat := 4983230072969 + 3 ^ 40 * 5670156 * 2
def baseEnd_5670156 : Nat := 107833904221297137861979

theorem tailTrace_5670156 : CollatzResearch.WordTrace tailWord_5670156 prefixEnd_5670156 107833904221297137861979 := by
  unfold tailWord_5670156
  simp only [CollatzResearch.WordTrace]
  refine ⟨103403789623000336196399161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137871719497333781595198881 103403789623000336196399161)
  ·
    refine ⟨77552842217250252147299371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103403789623000336196399161 77552842217250252147299371)
    ·
      refine ⟨116329263325875378220949057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77552842217250252147299371 116329263325875378220949057)
      ·
        refine ⟨87246947494406533665711793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116329263325875378220949057 87246947494406533665711793)
        ·
          refine ⟨65435210620804900249283845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87246947494406533665711793 65435210620804900249283845)
          ·
            refine ⟨12269101991400918796740721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65435210620804900249283845 12269101991400918796740721)
            ·
              refine ⟨9201826493550689097555541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12269101991400918796740721 9201826493550689097555541)
              ·
                refine ⟨107833904221297137861979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9201826493550689097555541 107833904221297137861979)
                ·
                  rfl

theorem cell23_5670156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 8].length) (baseStart_5670156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670156 prefixEnd_5670156 := by exact prefixLift 5670156
  have htrace : WordTrace (prefixWord ++ tailWord_5670156) baseStart_5670156 baseEnd_5670156 := by
    simpa [prefixWord, tailWord_5670156, baseEnd_5670156] using wordTrace_append hprefix tailTrace_5670156
  have hstable : (prefixWord ++ tailWord_5670156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670156).length < 2 ^ (prefixWord ++ tailWord_5670156).sum := by decide
  have hdescent : baseEnd_5670156 < baseStart_5670156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670170 : List Nat := [3, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3]
def baseStart_5670170 : Nat := 118140960795 + 5670170 * 2 ^ 59
def prefixEnd_5670170 : Nat := 4983230072969 + 3 ^ 40 * 5670170 * 2
def baseEnd_5670170 : Nat := 2911522602704185667498369

theorem tailTrace_5670170 : CollatzResearch.WordTrace tailWord_5670170 prefixEnd_5670170 2911522602704185667498369 := by
  unfold tailWord_5670170
  simp only [CollatzResearch.WordTrace]
  refine ⟨51702022466987488195951991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137872059911966635189205309 51702022466987488195951991)
  ·
    refine ⟨77553033700481232293927987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51702022466987488195951991 77553033700481232293927987)
    ·
      refine ⟨116329550550721848440891981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77553033700481232293927987 116329550550721848440891981)
      ·
        refine ⟨43623581456520693165334493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116329550550721848440891981 43623581456520693165334493)
        ·
          refine ⟨16358843046195259937000435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43623581456520693165334493 16358843046195259937000435)
          ·
            refine ⟨24538264569292889905500653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16358843046195259937000435 24538264569292889905500653)
            ·
              refine ⟨9201849213484833714562745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24538264569292889905500653 9201849213484833714562745)
              ·
                refine ⟨6901386910113625285922059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9201849213484833714562745 6901386910113625285922059)
                ·
                  refine ⟨10352080365170437928883089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6901386910113625285922059 10352080365170437928883089)
                  ·
                    refine ⟨7764060273877828446662317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10352080365170437928883089 7764060273877828446662317)
                    ·
                      refine ⟨2911522602704185667498369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7764060273877828446662317 2911522602704185667498369)
                      ·
                        rfl

theorem cell23_5670170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_5670170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670170 prefixEnd_5670170 := by exact prefixLift 5670170
  have htrace : WordTrace (prefixWord ++ tailWord_5670170) baseStart_5670170 baseEnd_5670170 := by
    simpa [prefixWord, tailWord_5670170, baseEnd_5670170] using wordTrace_append hprefix tailTrace_5670170
  have hstable : (prefixWord ++ tailWord_5670170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670170).length < 2 ^ (prefixWord ++ tailWord_5670170).sum := by decide
  have hdescent : baseEnd_5670170 < baseStart_5670170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670214 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_5670214 : Nat := 118140960795 + 5670214 * 2 ^ 59
def prefixEnd_5670214 : Nat := 4983230072969 + 3 ^ 40 * 5670214 * 2
def baseEnd_5670214 : Nat := 2911545195852983495348167

theorem tailTrace_5670214 : CollatzResearch.WordTrace tailWord_5670214 prefixEnd_5670214 2911545195852983495348167 := by
  unfold tailWord_5670214
  simp only [CollatzResearch.WordTrace]
  refine ⟨6462802958743454634325303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 137873129786527032198939797 6462802958743454634325303)
  ·
    refine ⟨9694204438115181951487955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6462802958743454634325303 9694204438115181951487955)
    ·
      refine ⟨14541306657172772927231933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9694204438115181951487955 14541306657172772927231933)
      ·
        refine ⟨5452989996439789847711975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14541306657172772927231933 5452989996439789847711975)
        ·
          refine ⟨8179484994659684771567963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5452989996439789847711975 8179484994659684771567963)
          ·
            refine ⟨12269227491989527157351945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8179484994659684771567963 12269227491989527157351945)
            ·
              refine ⟨9201920618992145368013959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12269227491989527157351945 9201920618992145368013959)
              ·
                refine ⟨13802880928488218052020939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9201920618992145368013959 13802880928488218052020939)
                ·
                  refine ⟨20704321392732327078031409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13802880928488218052020939 20704321392732327078031409)
                  ·
                    refine ⟨15528241044549245308523557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20704321392732327078031409 15528241044549245308523557)
                    ·
                      refine ⟨2911545195852983495348167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15528241044549245308523557 2911545195852983495348167)
                      ·
                        rfl

theorem cell23_5670214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_5670214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670214 prefixEnd_5670214 := by exact prefixLift 5670214
  have htrace : WordTrace (prefixWord ++ tailWord_5670214) baseStart_5670214 baseEnd_5670214 := by
    simpa [prefixWord, tailWord_5670214, baseEnd_5670214] using wordTrace_append hprefix tailTrace_5670214
  have hstable : (prefixWord ++ tailWord_5670214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670214).length < 2 ^ (prefixWord ++ tailWord_5670214).sum := by decide
  have hdescent : baseEnd_5670214 < baseStart_5670214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670240 : List Nat := [2, 1, 1, 3, 4, 1, 2, 2, 1, 4, 2]
def baseStart_5670240 : Nat := 118140960795 + 5670240 * 2 ^ 59
def prefixEnd_5670240 : Nat := 4983230072969 + 3 ^ 40 * 5670240 * 2
def baseEnd_5670240 : Nat := 2911558546350000393623047

theorem tailTrace_5670240 : CollatzResearch.WordTrace tailWord_5670240 prefixEnd_5670240 2911558546350000393623047 := by
  unfold tailWord_5670240
  simp only [CollatzResearch.WordTrace]
  refine ⟨103405321488848177369428087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137873761985130903159237449 103405321488848177369428087)
  ·
    refine ⟨155107982233272266054142131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103405321488848177369428087 155107982233272266054142131)
    ·
      refine ⟨232661973349908399081213197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155107982233272266054142131 232661973349908399081213197)
      ·
        refine ⟨87248240006215649655454949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232661973349908399081213197 87248240006215649655454949)
        ·
          refine ⟨16359045001165434310397803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87248240006215649655454949 16359045001165434310397803)
          ·
            refine ⟨24538567501748151465596705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16359045001165434310397803 24538567501748151465596705)
            ·
              refine ⟨18403925626311113599197529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24538567501748151465596705 18403925626311113599197529)
              ·
                refine ⟨13802944219733335199398147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18403925626311113599197529 13802944219733335199398147)
                ·
                  refine ⟨20704416329600002799097221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13802944219733335199398147 20704416329600002799097221)
                  ·
                    refine ⟨3882078061800000524830729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20704416329600002799097221 3882078061800000524830729)
                    ·
                      refine ⟨2911558546350000393623047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3882078061800000524830729 2911558546350000393623047)
                      ·
                        rfl

theorem cell23_5670240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_5670240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670240 prefixEnd_5670240 := by exact prefixLift 5670240
  have htrace : WordTrace (prefixWord ++ tailWord_5670240) baseStart_5670240 baseEnd_5670240 := by
    simpa [prefixWord, tailWord_5670240, baseEnd_5670240] using wordTrace_append hprefix tailTrace_5670240
  have hstable : (prefixWord ++ tailWord_5670240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670240).length < 2 ^ (prefixWord ++ tailWord_5670240).sum := by decide
  have hdescent : baseEnd_5670240 < baseStart_5670240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670244 : List Nat := [2, 3, 1, 1, 3, 4, 2, 1, 1, 3, 2]
def baseStart_5670244 : Nat := 118140960795 + 5670244 * 2 ^ 59
def prefixEnd_5670244 : Nat := 4983230072969 + 3 ^ 40 * 5670244 * 2
def baseEnd_5670244 : Nat := 2911560600272618377973029

theorem tailTrace_5670244 : CollatzResearch.WordTrace tailWord_5670244 prefixEnd_5670244 2911560600272618377973029 := by
  unfold tailWord_5670244
  simp only [CollatzResearch.WordTrace]
  refine ⟨103405394434840931711000893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137873859246454575614667857 103405394434840931711000893)
  ·
    refine ⟨38777022913065349391625335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103405394434840931711000893 38777022913065349391625335)
    ·
      refine ⟨58165534369598024087438003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38777022913065349391625335 58165534369598024087438003)
      ·
        refine ⟨87248301554397036131157005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58165534369598024087438003 87248301554397036131157005)
        ·
          refine ⟨32718113082898888549183877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87248301554397036131157005 32718113082898888549183877)
          ·
            refine ⟨6134646203043541602971977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32718113082898888549183877 6134646203043541602971977)
            ·
              refine ⟨4600984652282656202228983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6134646203043541602971977 4600984652282656202228983)
              ·
                refine ⟨6901476978423984303343475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4600984652282656202228983 6901476978423984303343475)
                ·
                  refine ⟨10352215467635976455015213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6901476978423984303343475 10352215467635976455015213)
                  ·
                    refine ⟨3882080800363491170630705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10352215467635976455015213 3882080800363491170630705)
                    ·
                      refine ⟨2911560600272618377973029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3882080800363491170630705 2911560600272618377973029)
                      ·
                        rfl

theorem cell23_5670244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_5670244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670244 prefixEnd_5670244 := by exact prefixLift 5670244
  have htrace : WordTrace (prefixWord ++ tailWord_5670244) baseStart_5670244 baseEnd_5670244 := by
    simpa [prefixWord, tailWord_5670244, baseEnd_5670244] using wordTrace_append hprefix tailTrace_5670244
  have hstable : (prefixWord ++ tailWord_5670244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670244).length < 2 ^ (prefixWord ++ tailWord_5670244).sum := by decide
  have hdescent : baseEnd_5670244 < baseStart_5670244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670253 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_5670253 : Nat := 118140960795 + 5670253 * 2 ^ 59
def prefixEnd_5670253 : Nat := 4983230072969 + 3 ^ 40 * 5670253 * 2
def baseEnd_5670253 : Nat := 2911565221598508842760487

theorem tailTrace_5670253 : CollatzResearch.WordTrace tailWord_5670253 prefixEnd_5670253 2911565221598508842760487 := by
  unfold tailWord_5670253
  simp only [CollatzResearch.WordTrace]
  refine ⟨206811117126649257959079413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137874078084432838639386275 206811117126649257959079413)
  ·
    refine ⟨19388542230623367933663695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206811117126649257959079413 19388542230623367933663695)
    ·
      refine ⟨29082813345935051900495543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19388542230623367933663695 29082813345935051900495543)
      ·
        refine ⟨43624220018902577850743315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29082813345935051900495543 43624220018902577850743315)
        ·
          refine ⟨65436330028353866776114973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43624220018902577850743315 65436330028353866776114973)
          ·
            refine ⟨24538623760632700041043115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65436330028353866776114973 24538623760632700041043115)
            ·
              refine ⟨36807935640949050061564673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24538623760632700041043115 36807935640949050061564673)
              ·
                refine ⟨27605951730711787546173505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36807935640949050061564673 27605951730711787546173505)
                ·
                  refine ⟨20704463798033840659630129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27605951730711787546173505 20704463798033840659630129)
                  ·
                    refine ⟨15528347848525380494722597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20704463798033840659630129 15528347848525380494722597)
                    ·
                      refine ⟨2911565221598508842760487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15528347848525380494722597 2911565221598508842760487)
                      ·
                        rfl

theorem cell23_5670253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_5670253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670253 prefixEnd_5670253 := by exact prefixLift 5670253
  have htrace : WordTrace (prefixWord ++ tailWord_5670253) baseStart_5670253 baseEnd_5670253 := by
    simpa [prefixWord, tailWord_5670253, baseEnd_5670253] using wordTrace_append hprefix tailTrace_5670253
  have hstable : (prefixWord ++ tailWord_5670253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670253).length < 2 ^ (prefixWord ++ tailWord_5670253).sum := by decide
  have hdescent : baseEnd_5670253 < baseStart_5670253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670257 : List Nat := [1, 2, 2, 2, 1, 2, 5, 2, 2, 2, 2]
def baseStart_5670257 : Nat := 118140960795 + 5670257 * 2 ^ 59
def prefixEnd_5670257 : Nat := 4983230072969 + 3 ^ 40 * 5670257 * 2
def baseEnd_5670257 : Nat := 2911567275521126827110469

theorem tailTrace_5670257 : CollatzResearch.WordTrace tailWord_5670257 prefixEnd_5670257 2911567275521126827110469 := by
  unfold tailWord_5670257
  simp only [CollatzResearch.WordTrace]
  refine ⟨206811263018634766642225025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137874175345756511094816683 206811263018634766642225025)
  ·
    refine ⟨155108447263976074981668769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206811263018634766642225025 155108447263976074981668769)
    ·
      refine ⟨116331335447982056236251577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155108447263976074981668769 116331335447982056236251577)
      ·
        refine ⟨87248501585986542177188683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116331335447982056236251577 87248501585986542177188683)
        ·
          refine ⟨130872752378979813265783025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87248501585986542177188683 130872752378979813265783025)
          ·
            refine ⟨98154564284234859949337269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130872752378979813265783025 98154564284234859949337269)
            ·
              refine ⟨9201990401647018120250369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98154564284234859949337269 9201990401647018120250369)
              ·
                refine ⟨6901492801235263590187777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9201990401647018120250369 6901492801235263590187777)
                ·
                  refine ⟨5176119600926447692640833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6901492801235263590187777 5176119600926447692640833)
                  ·
                    refine ⟨3882089700694835769480625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5176119600926447692640833 3882089700694835769480625)
                    ·
                      refine ⟨2911567275521126827110469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3882089700694835769480625 2911567275521126827110469)
                      ·
                        rfl

theorem cell23_5670257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2, 2, 2].length) (baseStart_5670257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670257 prefixEnd_5670257 := by exact prefixLift 5670257
  have htrace : WordTrace (prefixWord ++ tailWord_5670257) baseStart_5670257 baseEnd_5670257 := by
    simpa [prefixWord, tailWord_5670257, baseEnd_5670257] using wordTrace_append hprefix tailTrace_5670257
  have hstable : (prefixWord ++ tailWord_5670257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670257).length < 2 ^ (prefixWord ++ tailWord_5670257).sum := by decide
  have hdescent : baseEnd_5670257 < baseStart_5670257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670263 : List Nat := [1, 1, 3, 1, 1, 2, 3, 6, 5]
def baseStart_5670263 : Nat := 118140960795 + 5670263 * 2 ^ 59
def prefixEnd_5670263 : Nat := 4983230072969 + 3 ^ 40 * 5670263 * 2
def baseEnd_5670263 : Nat := 323507817378339311515049

theorem tailTrace_5670263 : CollatzResearch.WordTrace tailWord_5670263 prefixEnd_5670263 323507817378339311515049 := by
  unfold tailWord_5670263
  simp only [CollatzResearch.WordTrace]
  refine ⟨206811481856613029666943443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137874321237742019777962295 206811481856613029666943443)
  ·
    refine ⟨310217222784919544500415165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206811481856613029666943443 310217222784919544500415165)
    ·
      refine ⟨116331458544344829187655687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310217222784919544500415165 116331458544344829187655687)
      ·
        refine ⟨174497187816517243781483531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116331458544344829187655687 174497187816517243781483531)
        ·
          refine ⟨261745781724775865672225297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174497187816517243781483531 261745781724775865672225297)
          ·
            refine ⟨196309336293581899254168973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261745781724775865672225297 196309336293581899254168973)
            ·
              refine ⟨73616001110093212220313365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196309336293581899254168973 73616001110093212220313365)
              ·
                refine ⟨3450750052035619322827189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73616001110093212220313365 3450750052035619322827189)
                ·
                  refine ⟨323507817378339311515049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3450750052035619322827189 323507817378339311515049)
                  ·
                    rfl

theorem cell23_5670263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 6, 5].length) (baseStart_5670263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670263 prefixEnd_5670263 := by exact prefixLift 5670263
  have htrace : WordTrace (prefixWord ++ tailWord_5670263) baseStart_5670263 baseEnd_5670263 := by
    simpa [prefixWord, tailWord_5670263, baseEnd_5670263] using wordTrace_append hprefix tailTrace_5670263
  have hstable : (prefixWord ++ tailWord_5670263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670263).length < 2 ^ (prefixWord ++ tailWord_5670263).sum := by decide
  have hdescent : baseEnd_5670263 < baseStart_5670263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670274 : List Nat := [3, 4, 2, 1, 1, 1, 3, 1, 1, 4, 2]
def baseStart_5670274 : Nat := 118140960795 + 5670274 * 2 ^ 59
def prefixEnd_5670274 : Nat := 4983230072969 + 3 ^ 40 * 5670274 * 2
def baseEnd_5670274 : Nat := 2911576004692253260597891

theorem tailTrace_5670274 : CollatzResearch.WordTrace tailWord_5670274 prefixEnd_5670274 2911576004692253260597891 := by
  unfold tailWord_5670274
  simp only [CollatzResearch.WordTrace]
  refine ⟨51702970764893294636398469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137874588706382119030395917 51702970764893294636398469)
  ·
    refine ⟨9694307018417492744324713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51702970764893294636398469 9694307018417492744324713)
    ·
      refine ⟨7270730263813119558243535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9694307018417492744324713 7270730263813119558243535)
      ·
        refine ⟨10906095395719679337365303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7270730263813119558243535 10906095395719679337365303)
        ·
          refine ⟨16359143093579519006047955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10906095395719679337365303 16359143093579519006047955)
          ·
            refine ⟨24538714640369278509071933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16359143093579519006047955 24538714640369278509071933)
            ·
              refine ⟨9202017990138479440901975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24538714640369278509071933 9202017990138479440901975)
              ·
                refine ⟨13803026985207719161352963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9202017990138479440901975 13803026985207719161352963)
                ·
                  refine ⟨20704540477811578742029445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13803026985207719161352963 20704540477811578742029445)
                  ·
                    refine ⟨3882101339589671014130521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20704540477811578742029445 3882101339589671014130521)
                    ·
                      refine ⟨2911576004692253260597891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3882101339589671014130521 2911576004692253260597891)
                      ·
                        rfl

theorem cell23_5670274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_5670274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670274 prefixEnd_5670274 := by exact prefixLift 5670274
  have htrace : WordTrace (prefixWord ++ tailWord_5670274) baseStart_5670274 baseEnd_5670274 := by
    simpa [prefixWord, tailWord_5670274, baseEnd_5670274] using wordTrace_append hprefix tailTrace_5670274
  have hstable : (prefixWord ++ tailWord_5670274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670274).length < 2 ^ (prefixWord ++ tailWord_5670274).sum := by decide
  have hdescent : baseEnd_5670274 < baseStart_5670274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670350 : List Nat := [4, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3]
def baseStart_5670350 : Nat := 118140960795 + 5670350 * 2 ^ 59
def prefixEnd_5670350 : Nat := 4983230072969 + 3 ^ 40 * 5670350 * 2
def baseEnd_5670350 : Nat := 2911615029221994963247541

theorem tailTrace_5670350 : CollatzResearch.WordTrace tailWord_5670350 prefixEnd_5670350 2911615029221994963247541 := by
  unfold tailWord_5670350
  simp only [CollatzResearch.WordTrace]
  refine ⟨25851831875912230440670063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137876436671531895683573669 25851831875912230440670063)
  ·
    refine ⟨38777747813868345661005095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25851831875912230440670063 38777747813868345661005095)
    ·
      refine ⟨58166621720802518491507643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38777747813868345661005095 58166621720802518491507643)
      ·
        refine ⟨87249932581203777737261465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58166621720802518491507643 87249932581203777737261465)
        ·
          refine ⟨65437449435902833302946099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87249932581203777737261465 65437449435902833302946099)
          ·
            refine ⟨98156174153854249954419149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65437449435902833302946099 98156174153854249954419149)
            ·
              refine ⟨36808565307695343732907181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98156174153854249954419149 36808565307695343732907181)
              ·
                refine ⟨13803211990385753899840193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36808565307695343732907181 13803211990385753899840193)
                ·
                  refine ⟨10352408992789315424880145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13803211990385753899840193 10352408992789315424880145)
                  ·
                    refine ⟨7764306744591986568660109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10352408992789315424880145 7764306744591986568660109)
                    ·
                      refine ⟨2911615029221994963247541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7764306744591986568660109 2911615029221994963247541)
                      ·
                        rfl

theorem cell23_5670350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_5670350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670350 prefixEnd_5670350 := by exact prefixLift 5670350
  have htrace : WordTrace (prefixWord ++ tailWord_5670350) baseStart_5670350 baseEnd_5670350 := by
    simpa [prefixWord, tailWord_5670350, baseEnd_5670350] using wordTrace_append hprefix tailTrace_5670350
  have hstable : (prefixWord ++ tailWord_5670350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670350).length < 2 ^ (prefixWord ++ tailWord_5670350).sum := by decide
  have hdescent : baseEnd_5670350 < baseStart_5670350 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670357 : List Nat := [1, 3, 2, 3, 1, 1, 2, 5, 1, 4]
def baseStart_5670357 : Nat := 118140960795 + 5670357 * 2 ^ 59
def prefixEnd_5670357 : Nat := 4983230072969 + 3 ^ 40 * 5670357 * 2
def baseEnd_5670357 : Nat := 970539541195525478620003

theorem tailTrace_5670357 : CollatzResearch.WordTrace tailWord_5670357 prefixEnd_5670357 970539541195525478620003 := by
  unfold tailWord_5670357
  simp only [CollatzResearch.WordTrace]
  refine ⟨206814910318272483720865325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137876606878848322480576883 206814910318272483720865325)
  ·
    refine ⟨77555591369352181395324497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206814910318272483720865325 77555591369352181395324497)
    ·
      refine ⟨58166693527014136046493373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77555591369352181395324497 58166693527014136046493373)
      ·
        refine ⟨21812510072630301017435015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58166693527014136046493373 21812510072630301017435015)
        ·
          refine ⟨32718765108945451526152523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21812510072630301017435015 32718765108945451526152523)
          ·
            refine ⟨49078147663418177289228785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32718765108945451526152523 49078147663418177289228785)
            ·
              refine ⟨36808610747563632966921589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49078147663418177289228785 36808610747563632966921589)
              ·
                refine ⟨3450807257584090590648899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36808610747563632966921589 3450807257584090590648899)
                ·
                  refine ⟨5176210886376135885973349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3450807257584090590648899 5176210886376135885973349)
                  ·
                    refine ⟨970539541195525478620003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5176210886376135885973349 970539541195525478620003)
                    ·
                      rfl

theorem cell23_5670357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_5670357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670357 prefixEnd_5670357 := by exact prefixLift 5670357
  have htrace : WordTrace (prefixWord ++ tailWord_5670357) baseStart_5670357 baseEnd_5670357 := by
    simpa [prefixWord, tailWord_5670357, baseEnd_5670357] using wordTrace_append hprefix tailTrace_5670357
  have hstable : (prefixWord ++ tailWord_5670357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670357).length < 2 ^ (prefixWord ++ tailWord_5670357).sum := by decide
  have hdescent : baseEnd_5670357 < baseStart_5670357 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670383 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 3, 5]
def baseStart_5670383 : Nat := 118140960795 + 5670383 * 2 ^ 59
def prefixEnd_5670383 : Nat := 4983230072969 + 3 ^ 40 * 5670383 * 2
def baseEnd_5670383 : Nat := 970543991361197778044963

theorem tailTrace_5670383 : CollatzResearch.WordTrace tailWord_5670383 prefixEnd_5670383 970543991361197778044963 := by
  unfold tailWord_5670383
  simp only [CollatzResearch.WordTrace]
  refine ⟨206815858616178290161311803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137877239077452193440874535 206815858616178290161311803)
  ·
    refine ⟨310223787924267435241967705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206815858616178290161311803 310223787924267435241967705)
    ·
      refine ⟨232667840943200576431475779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310223787924267435241967705 232667840943200576431475779)
      ·
        refine ⟨349001761414800864647213669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232667840943200576431475779 349001761414800864647213669)
        ·
          refine ⟨65437830265275162121352563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 349001761414800864647213669 65437830265275162121352563)
          ·
            refine ⟨98156745397912743182028845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65437830265275162121352563 98156745397912743182028845)
            ·
              refine ⟨36808779524217278693260817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98156745397912743182028845 36808779524217278693260817)
              ·
                refine ⟨27606584643162959019945613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36808779524217278693260817 27606584643162959019945613)
                ·
                  refine ⟨10352469241186109632479605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27606584643162959019945613 10352469241186109632479605)
                  ·
                    refine ⟨970543991361197778044963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10352469241186109632479605 970543991361197778044963)
                    ·
                      rfl

theorem cell23_5670383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 5].length) (baseStart_5670383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670383 prefixEnd_5670383 := by exact prefixLift 5670383
  have htrace : WordTrace (prefixWord ++ tailWord_5670383) baseStart_5670383 baseEnd_5670383 := by
    simpa [prefixWord, tailWord_5670383, baseEnd_5670383] using wordTrace_append hprefix tailTrace_5670383
  have hstable : (prefixWord ++ tailWord_5670383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670383).length < 2 ^ (prefixWord ++ tailWord_5670383).sum := by decide
  have hdescent : baseEnd_5670383 < baseStart_5670383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670397 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 3, 1, 3]
def baseStart_5670397 : Nat := 118140960795 + 5670397 * 2 ^ 59
def prefixEnd_5670397 : Nat := 4983230072969 + 3 ^ 40 * 5670397 * 2
def baseEnd_5670397 : Nat := 2911639162812756279359825

theorem tailTrace_5670397 : CollatzResearch.WordTrace tailWord_5670397 prefixEnd_5670397 2911639162812756279359825 := by
  unfold tailWord_5670397
  simp only [CollatzResearch.WordTrace]
  refine ⟨206816369238127570552321445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137877579492085047034880963 206816369238127570552321445)
  ·
    refine ⟨38778069232148919478560271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206816369238127570552321445 38778069232148919478560271)
    ·
      refine ⟨58167103848223379217840407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38778069232148919478560271 58167103848223379217840407)
      ·
        refine ⟨87250655772335068826760611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58167103848223379217840407 87250655772335068826760611)
        ·
          refine ⟨130875983658502603240140917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87250655772335068826760611 130875983658502603240140917)
          ·
            refine ⟨12269623467984619053763211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 130875983658502603240140917 12269623467984619053763211)
            ·
              refine ⟨18404435201976928580644817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12269623467984619053763211 18404435201976928580644817)
              ·
                refine ⟨13803326401482696435483613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18404435201976928580644817 13803326401482696435483613)
                ·
                  refine ⟨5176247400556011163306355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13803326401482696435483613 5176247400556011163306355)
                  ·
                    refine ⟨7764371100834016744959533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5176247400556011163306355 7764371100834016744959533)
                    ·
                      refine ⟨2911639162812756279359825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7764371100834016744959533 2911639162812756279359825)
                      ·
                        rfl

theorem cell23_5670397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_5670397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670397 prefixEnd_5670397 := by exact prefixLift 5670397
  have htrace : WordTrace (prefixWord ++ tailWord_5670397) baseStart_5670397 baseEnd_5670397 := by
    simpa [prefixWord, tailWord_5670397, baseEnd_5670397] using wordTrace_append hprefix tailTrace_5670397
  have hstable : (prefixWord ++ tailWord_5670397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670397).length < 2 ^ (prefixWord ++ tailWord_5670397).sum := by decide
  have hdescent : baseEnd_5670397 < baseStart_5670397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670407 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 1, 5, 2]
def baseStart_5670407 : Nat := 118140960795 + 5670407 * 2 ^ 59
def prefixEnd_5670407 : Nat := 4983230072969 + 3 ^ 40 * 5670407 * 2
def baseEnd_5670407 : Nat := 2911644297619301240234779

theorem tailTrace_5670407 : CollatzResearch.WordTrace tailWord_5670407 prefixEnd_5670407 2911644297619301240234779 := by
  unfold tailWord_5670407
  simp only [CollatzResearch.WordTrace]
  refine ⟨206816733968091342260185475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137877822645394228173456983 206816733968091342260185475)
  ·
    refine ⟨310225100952137013390278213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206816733968091342260185475 310225100952137013390278213)
    ·
      refine ⟨58167206428525690010677165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310225100952137013390278213 58167206428525690010677165)
      ·
        refine ⟨21812702410697133754003937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58167206428525690010677165 21812702410697133754003937)
        ·
          refine ⟨16359526808022850315502953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21812702410697133754003937 16359526808022850315502953)
          ·
            refine ⟨12269645106017137736627215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16359526808022850315502953 12269645106017137736627215)
            ·
              refine ⟨18404467659025706604940823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12269645106017137736627215 18404467659025706604940823)
              ·
                refine ⟨27606701488538559907411235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18404467659025706604940823 27606701488538559907411235)
                ·
                  refine ⟨41410052232807839861116853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27606701488538559907411235 41410052232807839861116853)
                  ·
                    refine ⟨3882192396825734986979705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41410052232807839861116853 3882192396825734986979705)
                    ·
                      refine ⟨2911644297619301240234779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3882192396825734986979705 2911644297619301240234779)
                      ·
                        rfl

theorem cell23_5670407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_5670407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670407 prefixEnd_5670407 := by exact prefixLift 5670407
  have htrace : WordTrace (prefixWord ++ tailWord_5670407) baseStart_5670407 baseEnd_5670407 := by
    simpa [prefixWord, tailWord_5670407, baseEnd_5670407] using wordTrace_append hprefix tailTrace_5670407
  have hstable : (prefixWord ++ tailWord_5670407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670407).length < 2 ^ (prefixWord ++ tailWord_5670407).sum := by decide
  have hdescent : baseEnd_5670407 < baseStart_5670407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670457 : List Nat := [1, 2, 1, 5, 1, 2, 1, 4, 1, 2, 3]
def baseStart_5670457 : Nat := 118140960795 + 5670457 * 2 ^ 59
def prefixEnd_5670457 : Nat := 4983230072969 + 3 ^ 40 * 5670457 * 2
def baseEnd_5670457 : Nat := 2911669971652026044609549

theorem tailTrace_5670457 : CollatzResearch.WordTrace tailWord_5670457 prefixEnd_5670457 2911669971652026044609549 := by
  unfold tailWord_5670457
  simp only [CollatzResearch.WordTrace]
  refine ⟨206818557617910200799505625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137879038411940133866337083 206818557617910200799505625)
  ·
    refine ⟨155113918213432650599629219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206818557617910200799505625 155113918213432650599629219)
    ·
      refine ⟨232670877320148975899443829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155113918213432650599629219 232670877320148975899443829)
      ·
        refine ⟨21812894748763966490572859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 232670877320148975899443829 21812894748763966490572859)
        ·
          refine ⟨32719342123145949735859289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21812894748763966490572859 32719342123145949735859289)
          ·
            refine ⟨24539506592359462301894467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32719342123145949735859289 24539506592359462301894467)
            ·
              refine ⟨36809259888539193452841701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24539506592359462301894467 36809259888539193452841701)
              ·
                refine ⟨6901736229101098772407819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36809259888539193452841701 6901736229101098772407819)
                ·
                  refine ⟨10352604343651648158611729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6901736229101098772407819 10352604343651648158611729)
                  ·
                    refine ⟨7764453257738736118958797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10352604343651648158611729 7764453257738736118958797)
                    ·
                      refine ⟨2911669971652026044609549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7764453257738736118958797 2911669971652026044609549)
                      ·
                        rfl

theorem cell23_5670457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_5670457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670457 prefixEnd_5670457 := by exact prefixLift 5670457
  have htrace : WordTrace (prefixWord ++ tailWord_5670457) baseStart_5670457 baseEnd_5670457 := by
    simpa [prefixWord, tailWord_5670457, baseEnd_5670457] using wordTrace_append hprefix tailTrace_5670457
  have hstable : (prefixWord ++ tailWord_5670457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670457).length < 2 ^ (prefixWord ++ tailWord_5670457).sum := by decide
  have hdescent : baseEnd_5670457 < baseStart_5670457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670460 : List Nat := [2, 2, 2, 2, 4, 1, 1, 9]
def baseStart_5670460 : Nat := 118140960795 + 5670460 * 2 ^ 59
def prefixEnd_5670460 : Nat := 4983230072969 + 3 ^ 40 * 5670460 * 2
def baseEnd_5670460 : Nat := 107839685633110723439705

theorem tailTrace_5670460 : CollatzResearch.WordTrace tailWord_5670460 prefixEnd_5670460 107839685633110723439705 := by
  unfold tailWord_5670460
  simp only [CollatzResearch.WordTrace]
  refine ⟨103409333518449666155932417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137879111357932888207909889 103409333518449666155932417)
  ·
    refine ⟨77557000138837249616949313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103409333518449666155932417 77557000138837249616949313)
    ·
      refine ⟨58167750104127937212711985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77557000138837249616949313 58167750104127937212711985)
      ·
        refine ⟨43625812578095952909533989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58167750104127937212711985 43625812578095952909533989)
        ·
          refine ⟨8179839858392991170537623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43625812578095952909533989 8179839858392991170537623)
          ·
            refine ⟨12269759787589486755806435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8179839858392991170537623 12269759787589486755806435)
            ·
              refine ⟨18404639681384230133709653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12269759787589486755806435 18404639681384230133709653)
              ·
                refine ⟨107839685633110723439705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18404639681384230133709653 107839685633110723439705)
                ·
                  rfl

theorem cell23_5670460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 9].length) (baseStart_5670460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670460 prefixEnd_5670460 := by exact prefixLift 5670460
  have htrace : WordTrace (prefixWord ++ tailWord_5670460) baseStart_5670460 baseEnd_5670460 := by
    simpa [prefixWord, tailWord_5670460, baseEnd_5670460] using wordTrace_append hprefix tailTrace_5670460
  have hstable : (prefixWord ++ tailWord_5670460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670460).length < 2 ^ (prefixWord ++ tailWord_5670460).sum := by decide
  have hdescent : baseEnd_5670460 < baseStart_5670460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670477 : List Nat := [1, 6, 1, 1, 3, 2, 9]
def baseStart_5670477 : Nat := 118140960795 + 5670477 * 2 ^ 59
def prefixEnd_5670477 : Nat := 4983230072969 + 3 ^ 40 * 5670477 * 2
def baseEnd_5670477 : Nat := 35946669645248345263697

theorem tailTrace_5670477 : CollatzResearch.WordTrace tailWord_5670477 prefixEnd_5670477 35946669645248345263697 := by
  unfold tailWord_5670477
  simp only [CollatzResearch.WordTrace]
  refine ⟨206819287077837744215233685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137879524718558496143489123 206819287077837744215233685)
  ·
    refine ⟨9694654081773644260089079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 206819287077837744215233685 9694654081773644260089079)
    ·
      refine ⟨14541981122660466390133619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9694654081773644260089079 14541981122660466390133619)
      ·
        refine ⟨21812971683990699585200429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14541981122660466390133619 21812971683990699585200429)
        ·
          refine ⟨8179864381496512344450161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21812971683990699585200429 8179864381496512344450161)
          ·
            refine ⟨6134898286122384258337621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8179864381496512344450161 6134898286122384258337621)
            ·
              refine ⟨35946669645248345263697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6134898286122384258337621 35946669645248345263697)
              ·
                rfl

theorem cell23_5670477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 9].length) (baseStart_5670477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670477 prefixEnd_5670477 := by exact prefixLift 5670477
  have htrace : WordTrace (prefixWord ++ tailWord_5670477) baseStart_5670477 baseEnd_5670477 := by
    simpa [prefixWord, tailWord_5670477, baseEnd_5670477] using wordTrace_append hprefix tailTrace_5670477
  have hstable : (prefixWord ++ tailWord_5670477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670477).length < 2 ^ (prefixWord ++ tailWord_5670477).sum := by decide
  have hdescent : baseEnd_5670477 < baseStart_5670477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670487 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 4, 1, 3]
def baseStart_5670487 : Nat := 118140960795 + 5670487 * 2 ^ 59
def prefixEnd_5670487 : Nat := 4983230072969 + 3 ^ 40 * 5670487 * 2
def baseEnd_5670487 : Nat := 2911685376071660927234411

theorem tailTrace_5670487 : CollatzResearch.WordTrace tailWord_5670487 prefixEnd_5670487 2911685376071660927234411 := by
  unfold tailWord_5670487
  simp only [CollatzResearch.WordTrace]
  refine ⟨206819651807801515923097715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137879767871867677282065143 206819651807801515923097715)
  ·
    refine ⟨310229477711702273884646573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206819651807801515923097715 310229477711702273884646573)
    ·
      refine ⟨116336054141888352706742465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310229477711702273884646573 116336054141888352706742465)
      ·
        refine ⟨87252040606416264530056849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116336054141888352706742465 87252040606416264530056849)
        ·
          refine ⟨65439030454812198397542637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87252040606416264530056849 65439030454812198397542637)
          ·
            refine ⟨24539636420554574399078489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65439030454812198397542637 24539636420554574399078489)
            ·
              refine ⟨18404727315415930799308867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24539636420554574399078489 18404727315415930799308867)
              ·
                refine ⟨27607090973123896198963301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18404727315415930799308867 27607090973123896198963301)
                ·
                  refine ⟨5176329557460730537305619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27607090973123896198963301 5176329557460730537305619)
                  ·
                    refine ⟨7764494336191095805958429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5176329557460730537305619 7764494336191095805958429)
                    ·
                      refine ⟨2911685376071660927234411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7764494336191095805958429 2911685376071660927234411)
                      ·
                        rfl

theorem cell23_5670487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_5670487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670487 prefixEnd_5670487 := by exact prefixLift 5670487
  have htrace : WordTrace (prefixWord ++ tailWord_5670487) baseStart_5670487 baseEnd_5670487 := by
    simpa [prefixWord, tailWord_5670487, baseEnd_5670487] using wordTrace_append hprefix tailTrace_5670487
  have hstable : (prefixWord ++ tailWord_5670487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670487).length < 2 ^ (prefixWord ++ tailWord_5670487).sum := by decide
  have hdescent : baseEnd_5670487 < baseStart_5670487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670497 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 3, 3, 2]
def baseStart_5670497 : Nat := 118140960795 + 5670497 * 2 ^ 59
def prefixEnd_5670497 : Nat := 4983230072969 + 3 ^ 40 * 5670497 * 2
def baseEnd_5670497 : Nat := 2911690510878205888109365

theorem tailTrace_5670497 : CollatzResearch.WordTrace tailWord_5670497 prefixEnd_5670497 2911690510878205888109365 := by
  unfold tailWord_5670497
  simp only [CollatzResearch.WordTrace]
  refine ⟨206820016537765287630961745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137880011025176858420641163 206820016537765287630961745)
  ·
    refine ⟨155115012403323965723221309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206820016537765287630961745 155115012403323965723221309)
    ·
      refine ⟨58168129651246487146207991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155115012403323965723221309 58168129651246487146207991)
      ·
        refine ⟨87252194476869730719311987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58168129651246487146207991 87252194476869730719311987)
        ·
          refine ⟨130878291715304596078967981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87252194476869730719311987 130878291715304596078967981)
          ·
            refine ⟨49079359393239223529612993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130878291715304596078967981 49079359393239223529612993)
            ·
              refine ⟨36809519544929417647209745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49079359393239223529612993 36809519544929417647209745)
              ·
                refine ⟨27607139658697063235407309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36809519544929417647209745 27607139658697063235407309)
                ·
                  refine ⟨10352677372011398713277741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27607139658697063235407309 10352677372011398713277741)
                  ·
                    refine ⟨3882254014504274517479153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10352677372011398713277741 3882254014504274517479153)
                    ·
                      refine ⟨2911690510878205888109365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3882254014504274517479153 2911690510878205888109365)
                      ·
                        rfl

theorem cell23_5670497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_5670497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670497 prefixEnd_5670497 := by exact prefixLift 5670497
  have htrace : WordTrace (prefixWord ++ tailWord_5670497) baseStart_5670497 baseEnd_5670497 := by
    simpa [prefixWord, tailWord_5670497, baseEnd_5670497] using wordTrace_append hprefix tailTrace_5670497
  have hstable : (prefixWord ++ tailWord_5670497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670497).length < 2 ^ (prefixWord ++ tailWord_5670497).sum := by decide
  have hdescent : baseEnd_5670497 < baseStart_5670497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670514 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 3, 3, 2]
def baseStart_5670514 : Nat := 118140960795 + 5670514 * 2 ^ 59
def prefixEnd_5670514 : Nat := 4983230072969 + 3 ^ 40 * 5670514 * 2
def baseEnd_5670514 : Nat := 2911699240049332321596787

theorem tailTrace_5670514 : CollatzResearch.WordTrace tailWord_5670514 prefixEnd_5670514 2911699240049332321596787 := by
  unfold tailWord_5670514
  simp only [CollatzResearch.WordTrace]
  refine ⟨51705159144675924883582649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137880424385802466356220397 51705159144675924883582649)
  ·
    refine ⟨38778869358506943662686987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51705159144675924883582649 38778869358506943662686987)
    ·
      refine ⟨58168304037760415494030481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38778869358506943662686987 58168304037760415494030481)
      ·
        refine ⟨43626228028320311620522861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58168304037760415494030481 43626228028320311620522861)
        ·
          refine ⟨16359835510620116857696073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43626228028320311620522861 16359835510620116857696073)
          ·
            refine ⟨12269876632965087643272055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16359835510620116857696073 12269876632965087643272055)
            ·
              refine ⟨18404814949447631464908083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12269876632965087643272055 18404814949447631464908083)
              ·
                refine ⟨27607222424171447197362125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18404814949447631464908083 27607222424171447197362125)
                ·
                  refine ⟨10352708409064292699010797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27607222424171447197362125 10352708409064292699010797)
                  ·
                    refine ⟨3882265653399109762129049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10352708409064292699010797 3882265653399109762129049)
                    ·
                      refine ⟨2911699240049332321596787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3882265653399109762129049 2911699240049332321596787)
                      ·
                        rfl

theorem cell23_5670514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 3, 3, 2].length) (baseStart_5670514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670514 prefixEnd_5670514 := by exact prefixLift 5670514
  have htrace : WordTrace (prefixWord ++ tailWord_5670514) baseStart_5670514 baseEnd_5670514 := by
    simpa [prefixWord, tailWord_5670514, baseEnd_5670514] using wordTrace_append hprefix tailTrace_5670514
  have hstable : (prefixWord ++ tailWord_5670514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670514).length < 2 ^ (prefixWord ++ tailWord_5670514).sum := by decide
  have hdescent : baseEnd_5670514 < baseStart_5670514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670540 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 2, 2, 4]
def baseStart_5670540 : Nat := 118140960795 + 5670540 * 2 ^ 59
def prefixEnd_5670540 : Nat := 4983230072969 + 3 ^ 40 * 5670540 * 2
def baseEnd_5670540 : Nat := 2911712590546349219871667

theorem tailTrace_5670540 : CollatzResearch.WordTrace tailWord_5670540 prefixEnd_5670540 2911712590546349219871667 := by
  unfold tailWord_5670540
  simp only [CollatzResearch.WordTrace]
  refine ⟨103410792438304752987388537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137881056584406337316518049 103410792438304752987388537)
  ·
    refine ⟨77558094328728564740541403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103410792438304752987388537 77558094328728564740541403)
    ·
      refine ⟨116337141493092847110812105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77558094328728564740541403 116337141493092847110812105)
      ·
        refine ⟨87252856119819635333109079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116337141493092847110812105 87252856119819635333109079)
        ·
          refine ⟨130879284179729452999663619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87252856119819635333109079 130879284179729452999663619)
          ·
            refine ⟨196318926269594179499495429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130879284179729452999663619 196318926269594179499495429)
            ·
              refine ⟨36809798675548908656155393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196318926269594179499495429 36809798675548908656155393)
              ·
                refine ⟨27607349006661681492116545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36809798675548908656155393 27607349006661681492116545)
                ·
                  refine ⟨20705511754996261119087409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27607349006661681492116545 20705511754996261119087409)
                  ·
                    refine ⟨15529133816247195839315557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20705511754996261119087409 15529133816247195839315557)
                    ·
                      refine ⟨2911712590546349219871667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15529133816247195839315557 2911712590546349219871667)
                      ·
                        rfl

theorem cell23_5670540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_5670540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670540 prefixEnd_5670540 := by exact prefixLift 5670540
  have htrace : WordTrace (prefixWord ++ tailWord_5670540) baseStart_5670540 baseEnd_5670540 := by
    simpa [prefixWord, tailWord_5670540, baseEnd_5670540] using wordTrace_append hprefix tailTrace_5670540
  have hstable : (prefixWord ++ tailWord_5670540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670540).length < 2 ^ (prefixWord ++ tailWord_5670540).sum := by decide
  have hdescent : baseEnd_5670540 < baseStart_5670540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670561 : List Nat := [1, 2, 3, 3, 2, 1, 2, 3, 2, 2, 2]
def baseStart_5670561 : Nat := 118140960795 + 5670561 * 2 ^ 59
def prefixEnd_5670561 : Nat := 4983230072969 + 3 ^ 40 * 5670561 * 2
def baseEnd_5670561 : Nat := 2911723373640093637709071

theorem tailTrace_5670561 : CollatzResearch.WordTrace tailWord_5670561 prefixEnd_5670561 2911723373640093637709071 := by
  unfold tailWord_5670561
  simp only [CollatzResearch.WordTrace]
  refine ⟨206822350809533426561291537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137881567206355617707527691 206822350809533426561291537)
  ·
    refine ⟨155116763107150069920968653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206822350809533426561291537 155116763107150069920968653)
    ·
      refine ⟨58168786165181276220363245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155116763107150069920968653 58168786165181276220363245)
      ·
        refine ⟨21813294811942978582636217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58168786165181276220363245 21813294811942978582636217)
        ·
          refine ⟨16359971108957233936977163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21813294811942978582636217 16359971108957233936977163)
          ·
            refine ⟨24539956663435850905465745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16359971108957233936977163 24539956663435850905465745)
            ·
              refine ⟨18404967497576888179099309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24539956663435850905465745 18404967497576888179099309)
              ·
                refine ⟨6901862811591333067162241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18404967497576888179099309 6901862811591333067162241)
                ·
                  refine ⟨5176397108693499800371681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6901862811591333067162241 5176397108693499800371681)
                  ·
                    refine ⟨3882297831520124850278761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5176397108693499800371681 3882297831520124850278761)
                    ·
                      refine ⟨2911723373640093637709071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3882297831520124850278761 2911723373640093637709071)
                      ·
                        rfl

theorem cell23_5670561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_5670561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670561 prefixEnd_5670561 := by exact prefixLift 5670561
  have htrace : WordTrace (prefixWord ++ tailWord_5670561) baseStart_5670561 baseEnd_5670561 := by
    simpa [prefixWord, tailWord_5670561, baseEnd_5670561] using wordTrace_append hprefix tailTrace_5670561
  have hstable : (prefixWord ++ tailWord_5670561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670561).length < 2 ^ (prefixWord ++ tailWord_5670561).sum := by decide
  have hdescent : baseEnd_5670561 < baseStart_5670561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670684 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_5670684 : Nat := 118140960795 + 5670684 * 2 ^ 59
def prefixEnd_5670684 : Nat := 4983230072969 + 3 ^ 40 * 5670684 * 2
def baseEnd_5670684 : Nat := 2911786531760596656471005

theorem tailTrace_5670684 : CollatzResearch.WordTrace tailWord_5670684 prefixEnd_5670684 2911786531760596656471005 := by
  unfold tailWord_5670684
  simp only [CollatzResearch.WordTrace]
  refine ⟨103413418494043909284009553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137884557992058545712012737 103413418494043909284009553)
  ·
    refine ⟨77560063870532931963007165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103413418494043909284009553 77560063870532931963007165)
    ·
      refine ⟨29085023951449849486127687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77560063870532931963007165 29085023951449849486127687)
      ·
        refine ⟨43627535927174774229191531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29085023951449849486127687 43627535927174774229191531)
        ·
          refine ⟨65441303890762161343787297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43627535927174774229191531 65441303890762161343787297)
          ·
            refine ⟨49080977918071621007840473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65441303890762161343787297 49080977918071621007840473)
            ·
              refine ⟨36810733438553715755880355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49080977918071621007840473 36810733438553715755880355)
              ·
                refine ⟨55216100157830573633820533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36810733438553715755880355 55216100157830573633820533)
                ·
                  refine ⟨5176509389796616278170675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55216100157830573633820533 5176509389796616278170675)
                  ·
                    refine ⟨7764764084694924417256013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5176509389796616278170675 7764764084694924417256013)
                    ·
                      refine ⟨2911786531760596656471005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7764764084694924417256013 2911786531760596656471005)
                      ·
                        rfl

theorem cell23_5670684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_5670684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670684 prefixEnd_5670684 := by exact prefixLift 5670684
  have htrace : WordTrace (prefixWord ++ tailWord_5670684) baseStart_5670684 baseEnd_5670684 := by
    simpa [prefixWord, tailWord_5670684, baseEnd_5670684] using wordTrace_append hprefix tailTrace_5670684
  have hstable : (prefixWord ++ tailWord_5670684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670684).length < 2 ^ (prefixWord ++ tailWord_5670684).sum := by decide
  have hdescent : baseEnd_5670684 < baseStart_5670684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670687 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 3, 5]
def baseStart_5670687 : Nat := 118140960795 + 5670687 * 2 ^ 59
def prefixEnd_5670687 : Nat := 4983230072969 + 3 ^ 40 * 5670687 * 2
def baseEnd_5670687 : Nat := 970596024067520048244497

theorem tailTrace_5670687 : CollatzResearch.WordTrace tailWord_5670687 prefixEnd_5670687 970596024067520048244497 := by
  unfold tailWord_5670687
  simp only [CollatzResearch.WordTrace]
  refine ⟨206826946407076950080378315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137884630938051300053585543 206826946407076950080378315)
  ·
    refine ⟨310240419610615425120567473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206826946407076950080378315 310240419610615425120567473)
    ·
      refine ⟨232680314707961568840425605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310240419610615425120567473 232680314707961568840425605)
      ·
        refine ⟨43627559007742794157579801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 232680314707961568840425605 43627559007742794157579801)
        ·
          refine ⟨32720669255807095618184851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43627559007742794157579801 32720669255807095618184851)
          ·
            refine ⟨49081003883710643427277277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32720669255807095618184851 49081003883710643427277277)
            ·
              refine ⟨18405376456391491285228979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49081003883710643427277277 18405376456391491285228979)
              ·
                refine ⟨27608064684587236927843469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18405376456391491285228979 27608064684587236927843469)
                ·
                  refine ⟨10353024256720213847941301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27608064684587236927843469 10353024256720213847941301)
                  ·
                    refine ⟨970596024067520048244497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10353024256720213847941301 970596024067520048244497)
                    ·
                      rfl

theorem cell23_5670687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 5].length) (baseStart_5670687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670687 prefixEnd_5670687 := by exact prefixLift 5670687
  have htrace : WordTrace (prefixWord ++ tailWord_5670687) baseStart_5670687 baseEnd_5670687 := by
    simpa [prefixWord, tailWord_5670687, baseEnd_5670687] using wordTrace_append hprefix tailTrace_5670687
  have hstable : (prefixWord ++ tailWord_5670687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670687).length < 2 ^ (prefixWord ++ tailWord_5670687).sum := by decide
  have hdescent : baseEnd_5670687 < baseStart_5670687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670727 : List Nat := [1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_5670727 : Nat := 118140960795 + 5670727 * 2 ^ 59
def prefixEnd_5670727 : Nat := 4983230072969 + 3 ^ 40 * 5670727 * 2
def baseEnd_5670727 : Nat := 2911808611428739988233307

theorem tailTrace_5670727 : CollatzResearch.WordTrace tailWord_5670727 prefixEnd_5670727 2911808611428739988233307 := by
  unfold tailWord_5670727
  simp only [CollatzResearch.WordTrace]
  refine ⟨206828405326932036911834435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137885603551288024607889623 206828405326932036911834435)
  ·
    refine ⟨310242607990398055367751653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206828405326932036911834435 310242607990398055367751653)
    ·
      refine ⟨58170488998199635381453435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310242607990398055367751653 58170488998199635381453435)
      ·
        refine ⟨87255733497299453072180153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58170488998199635381453435 87255733497299453072180153)
        ·
          refine ⟨65441800122974589804135115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87255733497299453072180153 65441800122974589804135115)
          ·
            refine ⟨98162700184461884706202673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65441800122974589804135115 98162700184461884706202673)
            ·
              refine ⟨73622025138346413529652005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98162700184461884706202673 73622025138346413529652005)
              ·
                refine ⟨13804129713439952536809751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73622025138346413529652005 13804129713439952536809751)
                ·
                  refine ⟨20706194570159928805214627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13804129713439952536809751 20706194570159928805214627)
                  ·
                    refine ⟨31059291855239893207821941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20706194570159928805214627 31059291855239893207821941)
                    ·
                      refine ⟨2911808611428739988233307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31059291855239893207821941 2911808611428739988233307)
                      ·
                        rfl

theorem cell23_5670727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_5670727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670727 prefixEnd_5670727 := by exact prefixLift 5670727
  have htrace : WordTrace (prefixWord ++ tailWord_5670727) baseStart_5670727 baseEnd_5670727 := by
    simpa [prefixWord, tailWord_5670727, baseEnd_5670727] using wordTrace_append hprefix tailTrace_5670727
  have hstable : (prefixWord ++ tailWord_5670727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670727).length < 2 ^ (prefixWord ++ tailWord_5670727).sum := by decide
  have hdescent : baseEnd_5670727 < baseStart_5670727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670741 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 5, 2, 2]
def baseStart_5670741 : Nat := 118140960795 + 5670741 * 2 ^ 59
def prefixEnd_5670741 : Nat := 4983230072969 + 3 ^ 40 * 5670741 * 2
def baseEnd_5670741 : Nat := 2911815800157902933458243

theorem tailTrace_5670741 : CollatzResearch.WordTrace tailWord_5670741 prefixEnd_5670741 2911815800157902933458243 := by
  unfold tailWord_5670741
  simp only [CollatzResearch.WordTrace]
  refine ⟨206828915948881317302844077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137885943965920878201896051 206828915948881317302844077)
  ·
    refine ⟨77560843480830493988566529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206828915948881317302844077 77560843480830493988566529)
    ·
      refine ⟨58170632610622870491424897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77560843480830493988566529 58170632610622870491424897)
      ·
        refine ⟨43627974457967152868568673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58170632610622870491424897 43627974457967152868568673)
        ·
          refine ⟨32720980843475364651426505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43627974457967152868568673 32720980843475364651426505)
          ·
            refine ⟨24540735632606523488569879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32720980843475364651426505 24540735632606523488569879)
            ·
              refine ⟨36811103448909785232854819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24540735632606523488569879 36811103448909785232854819)
              ·
                refine ⟨55216655173364677849282229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36811103448909785232854819 55216655173364677849282229)
                ·
                  refine ⟨5176561422502938548370209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55216655173364677849282229 5176561422502938548370209)
                  ·
                    refine ⟨3882421066877203911277657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5176561422502938548370209 3882421066877203911277657)
                    ·
                      refine ⟨2911815800157902933458243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3882421066877203911277657 2911815800157902933458243)
                      ·
                        rfl

theorem cell23_5670741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_5670741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670741 prefixEnd_5670741 := by exact prefixLift 5670741
  have htrace : WordTrace (prefixWord ++ tailWord_5670741) baseStart_5670741 baseEnd_5670741 := by
    simpa [prefixWord, tailWord_5670741, baseEnd_5670741] using wordTrace_append hprefix tailTrace_5670741
  have hstable : (prefixWord ++ tailWord_5670741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670741).length < 2 ^ (prefixWord ++ tailWord_5670741).sum := by decide
  have hdescent : baseEnd_5670741 < baseStart_5670741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670785 : List Nat := [1, 2, 4, 4, 1, 1, 3, 1, 2, 4]
def baseStart_5670785 : Nat := 118140960795 + 5670785 * 2 ^ 59
def prefixEnd_5670785 : Nat := 4983230072969 + 3 ^ 40 * 5670785 * 2
def baseEnd_5670785 : Nat := 970612797768900253769347

theorem tailTrace_5670785 : CollatzResearch.WordTrace tailWord_5670785 prefixEnd_5670785 970612797768900253769347 := by
  unfold tailWord_5670785
  simp only [CollatzResearch.WordTrace]
  refine ⟨206830520760721912817445809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137887013840481275211630539 206830520760721912817445809)
  ·
    refine ⟨155122890570541434613084357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206830520760721912817445809 155122890570541434613084357)
    ·
      refine ⟨29085541981976518989953317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155122890570541434613084357 29085541981976518989953317)
      ·
        refine ⟨5453539121620597310616247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29085541981976518989953317 5453539121620597310616247)
        ·
          refine ⟨8180308682430895965924371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5453539121620597310616247 8180308682430895965924371)
          ·
            refine ⟨12270463023646343948886557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8180308682430895965924371 12270463023646343948886557)
            ·
              refine ⟨4601423633867378980832459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12270463023646343948886557 4601423633867378980832459)
              ·
                refine ⟨6902135450801068471248689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4601423633867378980832459 6902135450801068471248689)
                ·
                  refine ⟨5176601588100801353436517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6902135450801068471248689 5176601588100801353436517)
                  ·
                    refine ⟨970612797768900253769347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5176601588100801353436517 970612797768900253769347)
                    ·
                      rfl

theorem cell23_5670785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_5670785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670785 prefixEnd_5670785 := by exact prefixLift 5670785
  have htrace : WordTrace (prefixWord ++ tailWord_5670785) baseStart_5670785 baseEnd_5670785 := by
    simpa [prefixWord, tailWord_5670785, baseEnd_5670785] using wordTrace_append hprefix tailTrace_5670785
  have hstable : (prefixWord ++ tailWord_5670785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670785).length < 2 ^ (prefixWord ++ tailWord_5670785).sum := by decide
  have hdescent : baseEnd_5670785 < baseStart_5670785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670798 : List Nat := [4, 1, 1, 5, 1, 2, 2, 7]
def baseStart_5670798 : Nat := 118140960795 + 5670798 * 2 ^ 59
def prefixEnd_5670798 : Nat := 4983230072969 + 3 ^ 40 * 5670798 * 2
def baseEnd_5670798 : Nat := 107846113650192933720203

theorem tailTrace_5670798 : CollatzResearch.WordTrace tailWord_5670798 prefixEnd_5670798 107846113650192933720203 := by
  unfold tailWord_5670798
  simp only [CollatzResearch.WordTrace]
  refine ⟨25853874363709352004708631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137887329939783210691779365 25853874363709352004708631)
  ·
    refine ⟨38780811545564028007062947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25853874363709352004708631 38780811545564028007062947)
    ·
      refine ⟨58171217318346042010594421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38780811545564028007062947 58171217318346042010594421)
      ·
        refine ⟨5453551623594941438493227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58171217318346042010594421 5453551623594941438493227)
        ·
          refine ⟨8180327435392412157739841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5453551623594941438493227 8180327435392412157739841)
          ·
            refine ⟨6135245576544309118304881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8180327435392412157739841 6135245576544309118304881)
            ·
              refine ⟨4601434182408231838728661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6135245576544309118304881 4601434182408231838728661)
              ·
                refine ⟨107846113650192933720203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4601434182408231838728661 107846113650192933720203)
                ·
                  rfl

theorem cell23_5670798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 2, 7].length) (baseStart_5670798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670798 prefixEnd_5670798 := by exact prefixLift 5670798
  have htrace : WordTrace (prefixWord ++ tailWord_5670798) baseStart_5670798 baseEnd_5670798 := by
    simpa [prefixWord, tailWord_5670798, baseEnd_5670798] using wordTrace_append hprefix tailTrace_5670798
  have hstable : (prefixWord ++ tailWord_5670798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670798).length < 2 ^ (prefixWord ++ tailWord_5670798).sum := by decide
  have hdescent : baseEnd_5670798 < baseStart_5670798 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670801 : List Nat := [1, 2, 2, 1, 1, 1, 5, 4, 1, 3, 2]
def baseStart_5670801 : Nat := 118140960795 + 5670801 * 2 ^ 59
def prefixEnd_5670801 : Nat := 4983230072969 + 3 ^ 40 * 5670801 * 2
def baseEnd_5670801 : Nat := 2911846608997172698707967

theorem tailTrace_5670801 : CollatzResearch.WordTrace tailWord_5670801 prefixEnd_5670801 2911846608997172698707967 := by
  unfold tailWord_5670801
  simp only [CollatzResearch.WordTrace]
  refine ⟨206831104328663947550028257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137887402885775965033352171 206831104328663947550028257)
  ·
    refine ⟨155123328246497960662521193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206831104328663947550028257 155123328246497960662521193)
    ·
      refine ⟨116342496184873470496890895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155123328246497960662521193 116342496184873470496890895)
      ·
        refine ⟨174513744277310205745336343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116342496184873470496890895 174513744277310205745336343)
        ·
          refine ⟨261770616415965308618004515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174513744277310205745336343 261770616415965308618004515)
          ·
            refine ⟨392655924623947962927006773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261770616415965308618004515 392655924623947962927006773)
            ·
              refine ⟨36811492933495121524406885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 392655924623947962927006773 36811492933495121524406885)
              ·
                refine ⟨6902154925030335285826291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36811492933495121524406885 6902154925030335285826291)
                ·
                  refine ⟨10353232387545502928739437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6902154925030335285826291 10353232387545502928739437)
                  ·
                    refine ⟨3882462145329563598277289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10353232387545502928739437 3882462145329563598277289)
                    ·
                      refine ⟨2911846608997172698707967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3882462145329563598277289 2911846608997172698707967)
                      ·
                        rfl

theorem cell23_5670801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 3, 2].length) (baseStart_5670801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670801 prefixEnd_5670801 := by exact prefixLift 5670801
  have htrace : WordTrace (prefixWord ++ tailWord_5670801) baseStart_5670801 baseEnd_5670801 := by
    simpa [prefixWord, tailWord_5670801, baseEnd_5670801] using wordTrace_append hprefix tailTrace_5670801
  have hstable : (prefixWord ++ tailWord_5670801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670801).length < 2 ^ (prefixWord ++ tailWord_5670801).sum := by decide
  have hdescent : baseEnd_5670801 < baseStart_5670801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670804 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_5670804 : Nat := 118140960795 + 5670804 * 2 ^ 59
def prefixEnd_5670804 : Nat := 4983230072969 + 3 ^ 40 * 5670804 * 2
def baseEnd_5670804 : Nat := 2911848149439136186970453

theorem tailTrace_5670804 : CollatzResearch.WordTrace tailWord_5670804 prefixEnd_5670804 2911848149439136186970453 := by
  unfold tailWord_5670804
  simp only [CollatzResearch.WordTrace]
  refine ⟨103415606873826539531193733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137887475831768719374924977 103415606873826539531193733)
  ·
    refine ⟨19390426288842476162098825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103415606873826539531193733 19390426288842476162098825)
    ·
      refine ⟨14542819716631857121574119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19390426288842476162098825 14542819716631857121574119)
      ·
        refine ⟨21814229574947785682361179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14542819716631857121574119 21814229574947785682361179)
        ·
          refine ⟨32721344362421678523541769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21814229574947785682361179 32721344362421678523541769)
          ·
            refine ⟨24541008271816258892656327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32721344362421678523541769 24541008271816258892656327)
            ·
              refine ⟨36811512407724388338984491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24541008271816258892656327 36811512407724388338984491)
              ·
                refine ⟨55217268611586582508476737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36811512407724388338984491 55217268611586582508476737)
                ·
                  refine ⟨41412951458689936881357553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55217268611586582508476737 41412951458689936881357553)
                  ·
                    refine ⟨31059713594017452661018165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41412951458689936881357553 31059713594017452661018165)
                    ·
                      refine ⟨2911848149439136186970453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31059713594017452661018165 2911848149439136186970453)
                      ·
                        rfl

theorem cell23_5670804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_5670804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670804 prefixEnd_5670804 := by exact prefixLift 5670804
  have htrace : WordTrace (prefixWord ++ tailWord_5670804) baseStart_5670804 baseEnd_5670804 := by
    simpa [prefixWord, tailWord_5670804, baseEnd_5670804] using wordTrace_append hprefix tailTrace_5670804
  have hstable : (prefixWord ++ tailWord_5670804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670804).length < 2 ^ (prefixWord ++ tailWord_5670804).sum := by decide
  have hdescent : baseEnd_5670804 < baseStart_5670804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670831 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 4, 2, 2]
def baseStart_5670831 : Nat := 118140960795 + 5670831 * 2 ^ 59
def prefixEnd_5670831 : Nat := 4983230072969 + 3 ^ 40 * 5670831 * 2
def baseEnd_5670831 : Nat := 2911862013416807581332829

theorem tailTrace_5670831 : CollatzResearch.WordTrace tailWord_5670831 prefixEnd_5670831 2911862013416807581332829 := by
  unfold tailWord_5670831
  simp only [CollatzResearch.WordTrace]
  refine ⟨206832198518555262673620347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137888132345703508449080231 206832198518555262673620347)
  ·
    refine ⟨310248297777832894010430521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206832198518555262673620347 310248297777832894010430521)
    ·
      refine ⟨232686223333374670507822891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310248297777832894010430521 232686223333374670507822891)
      ·
        refine ⟨349029335000062005761734337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232686223333374670507822891 349029335000062005761734337)
        ·
          refine ⟨261772001250046504321300753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349029335000062005761734337 261772001250046504321300753)
          ·
            refine ⟨196329000937534878240975565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261772001250046504321300753 196329000937534878240975565)
            ·
              refine ⟨73623375351575579340365837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196329000937534878240975565 73623375351575579340365837)
              ·
                refine ⟨27608765756840842252637189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73623375351575579340365837 27608765756840842252637189)
                ·
                  refine ⟨5176643579407657922369473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27608765756840842252637189 5176643579407657922369473)
                  ·
                    refine ⟨3882482684555743441777105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5176643579407657922369473 3882482684555743441777105)
                    ·
                      refine ⟨2911862013416807581332829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3882482684555743441777105 2911862013416807581332829)
                      ·
                        rfl

theorem cell23_5670831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 4, 2, 2].length) (baseStart_5670831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670831 prefixEnd_5670831 := by exact prefixLift 5670831
  have htrace : WordTrace (prefixWord ++ tailWord_5670831) baseStart_5670831 baseEnd_5670831 := by
    simpa [prefixWord, tailWord_5670831, baseEnd_5670831] using wordTrace_append hprefix tailTrace_5670831
  have hstable : (prefixWord ++ tailWord_5670831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670831).length < 2 ^ (prefixWord ++ tailWord_5670831).sum := by decide
  have hdescent : baseEnd_5670831 < baseStart_5670831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670848 : List Nat := [2, 1, 1, 2, 3, 2, 3, 3, 2, 2, 2]
def baseStart_5670848 : Nat := 118140960795 + 5670848 * 2 ^ 59
def prefixEnd_5670848 : Nat := 4983230072969 + 3 ^ 40 * 5670848 * 2
def baseEnd_5670848 : Nat := 2911870742587934014820251

theorem tailTrace_5670848 : CollatzResearch.WordTrace tailWord_5670848 prefixEnd_5670848 2911870742587934014820251 := by
  unfold tailWord_5670848
  simp only [CollatzResearch.WordTrace]
  refine ⟨103416409279746837288494599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137888545706329116384659465 103416409279746837288494599)
  ·
    refine ⟨155124613919620255932741899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103416409279746837288494599 155124613919620255932741899)
    ·
      refine ⟨232686920879430383899112849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155124613919620255932741899 232686920879430383899112849)
      ·
        refine ⟨174515190659572787924334637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232686920879430383899112849 174515190659572787924334637)
        ·
          refine ⟨65443196497339795471625489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174515190659572787924334637 65443196497339795471625489)
          ·
            refine ⟨49082397373004846603719117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65443196497339795471625489 49082397373004846603719117)
            ·
              refine ⟨18405899014876817476394669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49082397373004846603719117 18405899014876817476394669)
              ·
                refine ⟨6902212130578806553648001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18405899014876817476394669 6902212130578806553648001)
                ·
                  refine ⟨5176659097934104915236001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6902212130578806553648001 5176659097934104915236001)
                  ·
                    refine ⟨3882494323450578686427001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5176659097934104915236001 3882494323450578686427001)
                    ·
                      refine ⟨2911870742587934014820251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3882494323450578686427001 2911870742587934014820251)
                      ·
                        rfl

theorem cell23_5670848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 2, 2, 2].length) (baseStart_5670848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670848 prefixEnd_5670848 := by exact prefixLift 5670848
  have htrace : WordTrace (prefixWord ++ tailWord_5670848) baseStart_5670848 baseEnd_5670848 := by
    simpa [prefixWord, tailWord_5670848, baseEnd_5670848] using wordTrace_append hprefix tailTrace_5670848
  have hstable : (prefixWord ++ tailWord_5670848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670848).length < 2 ^ (prefixWord ++ tailWord_5670848).sum := by decide
  have hdescent : baseEnd_5670848 < baseStart_5670848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670884 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 2, 5]
def baseStart_5670884 : Nat := 118140960795 + 5670884 * 2 ^ 59
def prefixEnd_5670884 : Nat := 4983230072969 + 3 ^ 40 * 5670884 * 2
def baseEnd_5670884 : Nat := 970629742630498624656695

theorem tailTrace_5670884 : CollatzResearch.WordTrace tailWord_5670884 prefixEnd_5670884 970629742630498624656695 := by
  unfold tailWord_5670884
  simp only [CollatzResearch.WordTrace]
  refine ⟨103417065793681626362649853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137889421058242168483533137 103417065793681626362649853)
  ·
    refine ⟨38781399672630609885993695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103417065793681626362649853 38781399672630609885993695)
    ·
      refine ⟨58172099508945914828990543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38781399672630609885993695 58172099508945914828990543)
      ·
        refine ⟨87258149263418872243485815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58172099508945914828990543 87258149263418872243485815)
        ·
          refine ⟨130887223895128308365228723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87258149263418872243485815 130887223895128308365228723)
          ·
            refine ⟨196330835842692462547843085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130887223895128308365228723 196330835842692462547843085)
            ·
              refine ⟨73624063441009673455441157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196330835842692462547843085 73624063441009673455441157)
              ·
                refine ⟨13804511895189313772895217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73624063441009673455441157 13804511895189313772895217)
                ·
                  refine ⟨10353383921391985329671413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13804511895189313772895217 10353383921391985329671413)
                  ·
                    refine ⟨970629742630498624656695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10353383921391985329671413 970629742630498624656695)
                    ·
                      rfl

theorem cell23_5670884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_5670884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670884 prefixEnd_5670884 := by exact prefixLift 5670884
  have htrace : WordTrace (prefixWord ++ tailWord_5670884) baseStart_5670884 baseEnd_5670884 := by
    simpa [prefixWord, tailWord_5670884, baseEnd_5670884] using wordTrace_append hprefix tailTrace_5670884
  have hstable : (prefixWord ++ tailWord_5670884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670884).length < 2 ^ (prefixWord ++ tailWord_5670884).sum := by decide
  have hdescent : baseEnd_5670884 < baseStart_5670884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5670904 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 4, 1, 4]
def baseStart_5670904 : Nat := 118140960795 + 5670904 * 2 ^ 59
def prefixEnd_5670904 : Nat := 4983230072969 + 3 ^ 40 * 5670904 * 2
def baseEnd_5670904 : Nat := 2911899497504585795719993

theorem tailTrace_5670904 : CollatzResearch.WordTrace tailWord_5670904 prefixEnd_5670904 2911899497504585795719993 := by
  unfold tailWord_5670904
  simp only [CollatzResearch.WordTrace]
  refine ⟨103417430523645398070513883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137889907364860530760685177 103417430523645398070513883)
  ·
    refine ⟨155126145785468097105770825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103417430523645398070513883 155126145785468097105770825)
    ·
      refine ⟨116344609339101072829328119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155126145785468097105770825 116344609339101072829328119)
      ·
        refine ⟨174516914008651609243992179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116344609339101072829328119 174516914008651609243992179)
        ·
          refine ⟨261775371012977413865988269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174516914008651609243992179 261775371012977413865988269)
          ·
            refine ⟨98165764129866530199745601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261775371012977413865988269 98165764129866530199745601)
            ·
              refine ⟨73624323097399897649809201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98165764129866530199745601 73624323097399897649809201)
              ·
                refine ⟨55218242323049923237356901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73624323097399897649809201 55218242323049923237356901)
                ·
                  refine ⟨10353420435571860607004419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55218242323049923237356901 10353420435571860607004419)
                  ·
                    refine ⟨15530130653357790910506629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10353420435571860607004419 15530130653357790910506629)
                    ·
                      refine ⟨2911899497504585795719993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15530130653357790910506629 2911899497504585795719993)
                      ·
                        rfl

theorem cell23_5670904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_5670904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5670904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5670904 prefixEnd_5670904 := by exact prefixLift 5670904
  have htrace : WordTrace (prefixWord ++ tailWord_5670904) baseStart_5670904 baseEnd_5670904 := by
    simpa [prefixWord, tailWord_5670904, baseEnd_5670904] using wordTrace_append hprefix tailTrace_5670904
  have hstable : (prefixWord ++ tailWord_5670904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5670904).length < 2 ^ (prefixWord ++ tailWord_5670904).sum := by decide
  have hdescent : baseEnd_5670904 < baseStart_5670904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5670904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671021 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_5671021 : Nat := 118140960795 + 5671021 * 2 ^ 59
def prefixEnd_5671021 : Nat := 4983230072969 + 3 ^ 40 * 5671021 * 2
def baseEnd_5671021 : Nat := 970653191580387279318985

theorem tailTrace_5671021 : CollatzResearch.WordTrace tailWord_5671021 prefixEnd_5671021 970653191580387279318985 := by
  unfold tailWord_5671021
  simp only [CollatzResearch.WordTrace]
  refine ⟨206839128387866925123036917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137892752258577950082024611 206839128387866925123036917)
  ·
    refine ⟨19391168286362524230284711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206839128387866925123036917 19391168286362524230284711)
    ·
      refine ⟨29086752429543786345427067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19391168286362524230284711 29086752429543786345427067)
      ·
        refine ⟨43630128644315679518140601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29086752429543786345427067 43630128644315679518140601)
        ·
          refine ⟨32722596483236759638605451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43630128644315679518140601 32722596483236759638605451)
          ·
            refine ⟨49083894724855139457908177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32722596483236759638605451 49083894724855139457908177)
            ·
              refine ⟨36812921043641354593431133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49083894724855139457908177 36812921043641354593431133)
              ·
                refine ⟨13804845391365507972536675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36812921043641354593431133 13804845391365507972536675)
                ·
                  refine ⟨20707268087048261958805013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13804845391365507972536675 20707268087048261958805013)
                  ·
                    refine ⟨970653191580387279318985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20707268087048261958805013 970653191580387279318985)
                    ·
                      rfl

theorem cell23_5671021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_5671021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671021 prefixEnd_5671021 := by exact prefixLift 5671021
  have htrace : WordTrace (prefixWord ++ tailWord_5671021) baseStart_5671021 baseEnd_5671021 := by
    simpa [prefixWord, tailWord_5671021, baseEnd_5671021] using wordTrace_append hprefix tailTrace_5671021
  have hstable : (prefixWord ++ tailWord_5671021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671021).length < 2 ^ (prefixWord ++ tailWord_5671021).sum := by decide
  have hdescent : baseEnd_5671021 < baseStart_5671021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671045 : List Nat := [1, 3, 1, 1, 5, 2, 3, 1, 1, 1, 4]
def baseStart_5671045 : Nat := 118140960795 + 5671045 * 2 ^ 59
def prefixEnd_5671045 : Nat := 4983230072969 + 3 ^ 40 * 5671045 * 2
def baseEnd_5671045 : Nat := 2911971898276869744056845

theorem tailTrace_5671045 : CollatzResearch.WordTrace tailWord_5671045 prefixEnd_5671045 2911971898276869744056845 := by
  unfold tailWord_5671045
  simp only [CollatzResearch.WordTrace]
  refine ⟨206840003739779977221910589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137893335826519984814607059 206840003739779977221910589)
  ·
    refine ⟨77565001402417491458216471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206840003739779977221910589 77565001402417491458216471)
    ·
      refine ⟨116347502103626237187324707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77565001402417491458216471 116347502103626237187324707)
      ·
        refine ⟨174521253155439355780987061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116347502103626237187324707 174521253155439355780987061)
        ·
          refine ⟨16361367483322439604467537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174521253155439355780987061 16361367483322439604467537)
          ·
            refine ⟨12271025612491829703350653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16361367483322439604467537 12271025612491829703350653)
            ·
              refine ⟨4601634604684436138756495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12271025612491829703350653 4601634604684436138756495)
              ·
                refine ⟨6902451907026654208134743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4601634604684436138756495 6902451907026654208134743)
                ·
                  refine ⟨10353677860539981312202115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6902451907026654208134743 10353677860539981312202115)
                  ·
                    refine ⟨15530516790809971968303173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10353677860539981312202115 15530516790809971968303173)
                    ·
                      refine ⟨2911971898276869744056845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15530516790809971968303173 2911971898276869744056845)
                      ·
                        rfl

theorem cell23_5671045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 1, 1, 4].length) (baseStart_5671045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671045 prefixEnd_5671045 := by exact prefixLift 5671045
  have htrace : WordTrace (prefixWord ++ tailWord_5671045) baseStart_5671045 baseEnd_5671045 := by
    simpa [prefixWord, tailWord_5671045, baseEnd_5671045] using wordTrace_append hprefix tailTrace_5671045
  have hstable : (prefixWord ++ tailWord_5671045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671045).length < 2 ^ (prefixWord ++ tailWord_5671045).sum := by decide
  have hdescent : baseEnd_5671045 < baseStart_5671045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671048 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 1, 1, 5]
def baseStart_5671048 : Nat := 118140960795 + 5671048 * 2 ^ 59
def prefixEnd_5671048 : Nat := 4983230072969 + 3 ^ 40 * 5671048 * 2
def baseEnd_5671048 : Nat := 2911973438718833232319331

theorem tailTrace_5671048 : CollatzResearch.WordTrace tailWord_5671048 prefixEnd_5671048 2911973438718833232319331 := by
  unfold tailWord_5671048
  simp only [CollatzResearch.WordTrace]
  refine ⟨103420056579384554367134899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137893408772512739156179865 103420056579384554367134899)
  ·
    refine ⟨155130084869076831550702349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103420056579384554367134899 155130084869076831550702349)
    ·
      refine ⟨58173781825903811831513381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155130084869076831550702349 58173781825903811831513381)
      ·
        refine ⟨10907584092356964718408759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58173781825903811831513381 10907584092356964718408759)
        ·
          refine ⟨16361376138535447077613139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10907584092356964718408759 16361376138535447077613139)
          ·
            refine ⟨24542064207803170616419709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16361376138535447077613139 24542064207803170616419709)
            ·
              refine ⟨9203274077926188981157391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24542064207803170616419709 9203274077926188981157391)
              ·
                refine ⟨13804911116889283471736087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9203274077926188981157391 13804911116889283471736087)
                ·
                  refine ⟨20707366675333925207604131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13804911116889283471736087 20707366675333925207604131)
                  ·
                    refine ⟨31061050013000887811406197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20707366675333925207604131 31061050013000887811406197)
                    ·
                      refine ⟨2911973438718833232319331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31061050013000887811406197 2911973438718833232319331)
                      ·
                        rfl

theorem cell23_5671048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_5671048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671048 prefixEnd_5671048 := by exact prefixLift 5671048
  have htrace : WordTrace (prefixWord ++ tailWord_5671048) baseStart_5671048 baseEnd_5671048 := by
    simpa [prefixWord, tailWord_5671048, baseEnd_5671048] using wordTrace_append hprefix tailTrace_5671048
  have hstable : (prefixWord ++ tailWord_5671048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671048).length < 2 ^ (prefixWord ++ tailWord_5671048).sum := by decide
  have hdescent : baseEnd_5671048 < baseStart_5671048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671061 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 3, 3, 3]
def baseStart_5671061 : Nat := 118140960795 + 5671061 * 2 ^ 59
def prefixEnd_5671061 : Nat := 4983230072969 + 3 ^ 40 * 5671061 * 2
def baseEnd_5671061 : Nat := 2911980113967341681456771

theorem tailTrace_5671061 : CollatzResearch.WordTrace tailWord_5671061 prefixEnd_5671061 2911980113967341681456771 := by
  unfold tailWord_5671061
  simp only [CollatzResearch.WordTrace]
  refine ⟨206840587307722011954493037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137893724871814674636328691 206840587307722011954493037)
  ·
    refine ⟨77565220240395754482934889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206840587307722011954493037 77565220240395754482934889)
    ·
      refine ⟨58173915180296815862201167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77565220240395754482934889 58173915180296815862201167)
      ·
        refine ⟨87260872770445223793301751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58173915180296815862201167 87260872770445223793301751)
        ·
          refine ⟨130891309155667835689952627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87260872770445223793301751 130891309155667835689952627)
          ·
            refine ⟨196336963733501753534928941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130891309155667835689952627 196336963733501753534928941)
            ·
              refine ⟨73626361400063157575598353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196336963733501753534928941 73626361400063157575598353)
              ·
                refine ⟨55219771050047368181698765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73626361400063157575598353 55219771050047368181698765)
                ·
                  refine ⟨20707414143767763068137037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55219771050047368181698765 20707414143767763068137037)
                  ·
                    refine ⟨7765280303912911150551389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20707414143767763068137037 7765280303912911150551389)
                    ·
                      refine ⟨2911980113967341681456771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7765280303912911150551389 2911980113967341681456771)
                      ·
                        rfl

theorem cell23_5671061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_5671061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671061 prefixEnd_5671061 := by exact prefixLift 5671061
  have htrace : WordTrace (prefixWord ++ tailWord_5671061) baseStart_5671061 baseEnd_5671061 := by
    simpa [prefixWord, tailWord_5671061, baseEnd_5671061] using wordTrace_append hprefix tailTrace_5671061
  have hstable : (prefixWord ++ tailWord_5671061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671061).length < 2 ^ (prefixWord ++ tailWord_5671061).sum := by decide
  have hdescent : baseEnd_5671061 < baseStart_5671061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671121 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 1, 6, 3]
def baseStart_5671121 : Nat := 118140960795 + 5671121 * 2 ^ 59
def prefixEnd_5671121 : Nat := 4983230072969 + 3 ^ 40 * 5671121 * 2
def baseEnd_5671121 : Nat := 2912010922806611446706495

theorem tailTrace_5671121 : CollatzResearch.WordTrace tailWord_5671121 prefixEnd_5671121 2912010922806611446706495 := by
  unfold tailWord_5671121
  simp only [CollatzResearch.WordTrace]
  refine ⟨206842775687504642201677217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137895183791669761467784811 206842775687504642201677217)
  ·
    refine ⟨155132081765628481651257913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206842775687504642201677217 155132081765628481651257913)
    ·
      refine ⟨116349061324221361238443435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155132081765628481651257913 116349061324221361238443435)
      ·
        refine ⟨174523591986332041857665153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116349061324221361238443435 174523591986332041857665153)
        ·
          refine ⟨130892693989749031393248865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174523591986332041857665153 130892693989749031393248865)
          ·
            refine ⟨98169520492311773544936649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130892693989749031393248865 98169520492311773544936649)
            ·
              refine ⟨73627140369233830158702487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98169520492311773544936649 73627140369233830158702487)
              ·
                refine ⟨110440710553850745238053731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73627140369233830158702487 110440710553850745238053731)
                ·
                  refine ⟨165661065830776117857080597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110440710553850745238053731 165661065830776117857080597)
                  ·
                    refine ⟨7765362460817630524550653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 165661065830776117857080597 7765362460817630524550653)
                    ·
                      refine ⟨2912010922806611446706495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7765362460817630524550653 2912010922806611446706495)
                      ·
                        rfl

theorem cell23_5671121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 6, 3].length) (baseStart_5671121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671121 prefixEnd_5671121 := by exact prefixLift 5671121
  have htrace : WordTrace (prefixWord ++ tailWord_5671121) baseStart_5671121 baseEnd_5671121 := by
    simpa [prefixWord, tailWord_5671121, baseEnd_5671121] using wordTrace_append hprefix tailTrace_5671121
  have hstable : (prefixWord ++ tailWord_5671121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671121).length < 2 ^ (prefixWord ++ tailWord_5671121).sum := by decide
  have hdescent : baseEnd_5671121 < baseStart_5671121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671139 : List Nat := [1, 1, 1, 8, 1, 1, 2, 2, 1, 3, 2]
def baseStart_5671139 : Nat := 118140960795 + 5671139 * 2 ^ 59
def prefixEnd_5671139 : Nat := 4983230072969 + 3 ^ 40 * 5671139 * 2
def baseEnd_5671139 : Nat := 2912020165458392376281413

theorem tailTrace_5671139 : CollatzResearch.WordTrace tailWord_5671139 prefixEnd_5671139 2912020165458392376281413 := by
  unfold tailWord_5671139
  simp only [CollatzResearch.WordTrace]
  refine ⟨206843432201439431275832471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137895621467626287517221647 206843432201439431275832471)
  ·
    refine ⟨310265148302159146913748707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206843432201439431275832471 310265148302159146913748707)
    ·
      refine ⟨465397722453238720370623061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310265148302159146913748707 465397722453238720370623061)
      ·
        refine ⟨5453879559998891254343239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 465397722453238720370623061 5453879559998891254343239)
        ·
          refine ⟨8180819339998336881514859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5453879559998891254343239 8180819339998336881514859)
          ·
            refine ⟨12271229009997505322272289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8180819339998336881514859 12271229009997505322272289)
            ·
              refine ⟨9203421757498128991704217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12271229009997505322272289 9203421757498128991704217)
              ·
                refine ⟨6902566318123596743778163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9203421757498128991704217 6902566318123596743778163)
                ·
                  refine ⟨10353849477185395115667245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6902566318123596743778163 10353849477185395115667245)
                  ·
                    refine ⟨3882693553944523168375217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10353849477185395115667245 3882693553944523168375217)
                    ·
                      refine ⟨2912020165458392376281413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3882693553944523168375217 2912020165458392376281413)
                      ·
                        rfl

theorem cell23_5671139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_5671139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671139 prefixEnd_5671139 := by exact prefixLift 5671139
  have htrace : WordTrace (prefixWord ++ tailWord_5671139) baseStart_5671139 baseEnd_5671139 := by
    simpa [prefixWord, tailWord_5671139, baseEnd_5671139] using wordTrace_append hprefix tailTrace_5671139
  have hstable : (prefixWord ++ tailWord_5671139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671139).length < 2 ^ (prefixWord ++ tailWord_5671139).sum := by decide
  have hdescent : baseEnd_5671139 < baseStart_5671139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671201 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 2, 8]
def baseStart_5671201 : Nat := 118140960795 + 5671201 * 2 ^ 59
def prefixEnd_5671201 : Nat := 4983230072969 + 3 ^ 40 * 5671201 * 2
def baseEnd_5671201 : Nat := 970684000419657044568709

theorem tailTrace_5671201 : CollatzResearch.WordTrace tailWord_5671201 prefixEnd_5671201 970684000419657044568709 := by
  unfold tailWord_5671201
  simp only [CollatzResearch.WordTrace]
  refine ⟨206845693527214815864589457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137897129018143210576392971 206845693527214815864589457)
  ·
    refine ⟨155134270145411111898442093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206845693527214815864589457 155134270145411111898442093)
    ·
      refine ⟨58175351304529166961915785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155134270145411111898442093 58175351304529166961915785)
      ·
        refine ⟨43631513478396875221436839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58175351304529166961915785 43631513478396875221436839)
        ·
          refine ⟨65447270217595312832155259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43631513478396875221436839 65447270217595312832155259)
          ·
            refine ⟨98170905326392969248232889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65447270217595312832155259 98170905326392969248232889)
            ·
              refine ⟨73628178994794726936174667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98170905326392969248232889 73628178994794726936174667)
              ·
                refine ⟨110442268492192090404262001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73628178994794726936174667 110442268492192090404262001)
                ·
                  refine ⟨82831701369144067803196501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110442268492192090404262001 82831701369144067803196501)
                  ·
                    refine ⟨970684000419657044568709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82831701369144067803196501 970684000419657044568709)
                    ·
                      rfl

theorem cell23_5671201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_5671201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671201 prefixEnd_5671201 := by exact prefixLift 5671201
  have htrace : WordTrace (prefixWord ++ tailWord_5671201) baseStart_5671201 baseEnd_5671201 := by
    simpa [prefixWord, tailWord_5671201, baseEnd_5671201] using wordTrace_append hprefix tailTrace_5671201
  have hstable : (prefixWord ++ tailWord_5671201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671201).length < 2 ^ (prefixWord ++ tailWord_5671201).sum := by decide
  have hdescent : baseEnd_5671201 < baseStart_5671201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671205 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 2, 5]
def baseStart_5671205 : Nat := 118140960795 + 5671205 * 2 ^ 59
def prefixEnd_5671205 : Nat := 4983230072969 + 3 ^ 40 * 5671205 * 2
def baseEnd_5671205 : Nat := 970684685060529706018703

theorem tailTrace_5671205 : CollatzResearch.WordTrace tailWord_5671205 prefixEnd_5671205 970684685060529706018703 := by
  unfold tailWord_5671205
  simp only [CollatzResearch.WordTrace]
  refine ⟨206845839419200324547735069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137897226279466883031823379 206845839419200324547735069)
  ·
    refine ⟨77567189782200121705400651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206845839419200324547735069 77567189782200121705400651)
    ·
      refine ⟨116350784673300182558100977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77567189782200121705400651 116350784673300182558100977)
      ·
        refine ⟨87263088504975136918575733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116350784673300182558100977 87263088504975136918575733)
        ·
          refine ⟨8180914547341419086116475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87263088504975136918575733 8180914547341419086116475)
          ·
            refine ⟨12271371821012128629174713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8180914547341419086116475 12271371821012128629174713)
            ·
              refine ⟨9203528865759096471881035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12271371821012128629174713 9203528865759096471881035)
              ·
                refine ⟨13805293298638644707821553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9203528865759096471881035 13805293298638644707821553)
                ·
                  refine ⟨10353969973978983530866165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13805293298638644707821553 10353969973978983530866165)
                  ·
                    refine ⟨970684685060529706018703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10353969973978983530866165 970684685060529706018703)
                    ·
                      rfl

theorem cell23_5671205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_5671205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671205 prefixEnd_5671205 := by exact prefixLift 5671205
  have htrace : WordTrace (prefixWord ++ tailWord_5671205) baseStart_5671205 baseEnd_5671205 := by
    simpa [prefixWord, tailWord_5671205, baseEnd_5671205] using wordTrace_append hprefix tailTrace_5671205
  have hstable : (prefixWord ++ tailWord_5671205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671205).length < 2 ^ (prefixWord ++ tailWord_5671205).sum := by decide
  have hdescent : baseEnd_5671205 < baseStart_5671205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671225 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 2, 1, 4]
def baseStart_5671225 : Nat := 118140960795 + 5671225 * 2 ^ 59
def prefixEnd_5671225 : Nat := 4983230072969 + 3 ^ 40 * 5671225 * 2
def baseEnd_5671225 : Nat := 2912064324794679039806017

theorem tailTrace_5671225 : CollatzResearch.WordTrace tailWord_5671225 prefixEnd_5671225 2912064324794679039806017 := by
  unfold tailWord_5671225
  simp only [CollatzResearch.WordTrace]
  refine ⟨206846568879127867963463129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137897712586085245308975419 206846568879127867963463129)
  ·
    refine ⟨155134926659345900972597347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206846568879127867963463129 155134926659345900972597347)
    ·
      refine ⟨232702389989018851458896021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155134926659345900972597347 232702389989018851458896021)
      ·
        refine ⟨10907924530735258662135751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 232702389989018851458896021 10907924530735258662135751)
        ·
          refine ⟨16361886796102887993203627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10907924530735258662135751 16361886796102887993203627)
          ·
            refine ⟨24542830194154331989805441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16361886796102887993203627 24542830194154331989805441)
            ·
              refine ⟨18407122645615748992354081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24542830194154331989805441 18407122645615748992354081)
              ·
                refine ⟨13805341984211811744265561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18407122645615748992354081 13805341984211811744265561)
                ·
                  refine ⟨10354006488158858808199171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13805341984211811744265561 10354006488158858808199171)
                  ·
                    refine ⟨15531009732238288212298757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10354006488158858808199171 15531009732238288212298757)
                    ·
                      refine ⟨2912064324794679039806017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15531009732238288212298757 2912064324794679039806017)
                      ·
                        rfl

theorem cell23_5671225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_5671225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671225 prefixEnd_5671225 := by exact prefixLift 5671225
  have htrace : WordTrace (prefixWord ++ tailWord_5671225) baseStart_5671225 baseEnd_5671225 := by
    simpa [prefixWord, tailWord_5671225, baseEnd_5671225] using wordTrace_append hprefix tailTrace_5671225
  have hstable : (prefixWord ++ tailWord_5671225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671225).length < 2 ^ (prefixWord ++ tailWord_5671225).sum := by decide
  have hdescent : baseEnd_5671225 < baseStart_5671225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671248 : List Nat := [2, 1, 1, 1, 1, 6, 2, 3, 6]
def baseStart_5671248 : Nat := 118140960795 + 5671248 * 2 ^ 59
def prefixEnd_5671248 : Nat := 4983230072969 + 3 ^ 40 * 5671248 * 2
def baseEnd_5671248 : Nat := 323564014983303605535379

theorem tailTrace_5671248 : CollatzResearch.WordTrace tailWord_5671248 prefixEnd_5671248 323564014983303605535379 := by
  unfold tailWord_5671248
  simp only [CollatzResearch.WordTrace]
  refine ⟨103423703879022271445775199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137898271838696361927700265 103423703879022271445775199)
  ·
    refine ⟨155135555818533407168662799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103423703879022271445775199 155135555818533407168662799)
    ·
      refine ⟨232703333727800110752994199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155135555818533407168662799 232703333727800110752994199)
      ·
        refine ⟨349055000591700166129491299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232703333727800110752994199 349055000591700166129491299)
        ·
          refine ⟨523582500887550249194236949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349055000591700166129491299 523582500887550249194236949)
          ·
            refine ⟨24542929729103917930979857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 523582500887550249194236949 24542929729103917930979857)
            ·
              refine ⟨18407197296827938448234893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24542929729103917930979857 18407197296827938448234893)
              ·
                refine ⟨6902698986310476918088085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18407197296827938448234893 6902698986310476918088085)
                ·
                  refine ⟨323564014983303605535379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6902698986310476918088085 323564014983303605535379)
                  ·
                    rfl

theorem cell23_5671248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 3, 6].length) (baseStart_5671248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671248 prefixEnd_5671248 := by exact prefixLift 5671248
  have htrace : WordTrace (prefixWord ++ tailWord_5671248) baseStart_5671248 baseEnd_5671248 := by
    simpa [prefixWord, tailWord_5671248, baseEnd_5671248] using wordTrace_append hprefix tailTrace_5671248
  have hstable : (prefixWord ++ tailWord_5671248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671248).length < 2 ^ (prefixWord ++ tailWord_5671248).sum := by decide
  have hdescent : baseEnd_5671248 < baseStart_5671248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671251 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 6]
def baseStart_5671251 : Nat := 118140960795 + 5671251 * 2 ^ 59
def prefixEnd_5671251 : Nat := 4983230072969 + 3 ^ 40 * 5671251 * 2
def baseEnd_5671251 : Nat := 2912077675291695938080897

theorem tailTrace_5671251 : CollatzResearch.WordTrace tailWord_5671251 prefixEnd_5671251 2912077675291695938080897 := by
  unfold tailWord_5671251
  simp only [CollatzResearch.WordTrace]
  refine ⟨206847517177033674403909607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137898344784689116269273071 206847517177033674403909607)
  ·
    refine ⟨310271275765550511605864411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206847517177033674403909607 310271275765550511605864411)
    ·
      refine ⟨465406913648325767408796617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310271275765550511605864411 465406913648325767408796617)
      ·
        refine ⟨349055185236244325556597463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465406913648325767408796617 349055185236244325556597463)
        ·
          refine ⟨523582777854366488334896195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349055185236244325556597463 523582777854366488334896195)
          ·
            refine ⟨785374166781549732502344293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523582777854366488334896195 785374166781549732502344293)
            ·
              refine ⟨147257656271540574844189555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 785374166781549732502344293 147257656271540574844189555)
              ·
                refine ⟨220886484407310862266284333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147257656271540574844189555 220886484407310862266284333)
                ·
                  refine ⟨82832431652741573349856625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 220886484407310862266284333 82832431652741573349856625)
                  ·
                    refine ⟨62124323739556180012392469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 82832431652741573349856625 62124323739556180012392469)
                    ·
                      refine ⟨2912077675291695938080897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62124323739556180012392469 2912077675291695938080897)
                      ·
                        rfl

theorem cell23_5671251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_5671251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671251 prefixEnd_5671251 := by exact prefixLift 5671251
  have htrace : WordTrace (prefixWord ++ tailWord_5671251) baseStart_5671251 baseEnd_5671251 := by
    simpa [prefixWord, tailWord_5671251, baseEnd_5671251] using wordTrace_append hprefix tailTrace_5671251
  have hstable : (prefixWord ++ tailWord_5671251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671251).length < 2 ^ (prefixWord ++ tailWord_5671251).sum := by decide
  have hdescent : baseEnd_5671251 < baseStart_5671251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671332 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 5, 2, 2]
def baseStart_5671332 : Nat := 118140960795 + 5671332 * 2 ^ 59
def prefixEnd_5671332 : Nat := 4983230072969 + 3 ^ 40 * 5671332 * 2
def baseEnd_5671332 : Nat := 2912119267224710121168025

theorem tailTrace_5671332 : CollatzResearch.WordTrace tailWord_5671332 prefixEnd_5671332 2912119267224710121168025 := by
  unfold tailWord_5671332
  simp only [CollatzResearch.WordTrace]
  refine ⟨103425235744870112618804125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137900314326493483491738833 103425235744870112618804125)
  ·
    refine ⟨38784463404326292232051547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103425235744870112618804125 38784463404326292232051547)
    ·
      refine ⟨58176695106489438348077321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38784463404326292232051547 58176695106489438348077321)
      ·
        refine ⟨43632521329867078761057991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58176695106489438348077321 43632521329867078761057991)
        ·
          refine ⟨65448781994800618141586987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43632521329867078761057991 65448781994800618141586987)
          ·
            refine ⟨98173172992200927212380481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65448781994800618141586987 98173172992200927212380481)
            ·
              refine ⟨73629879744150695409285361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98173172992200927212380481 73629879744150695409285361)
              ·
                refine ⟨55222409808113021556964021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73629879744150695409285361 55222409808113021556964021)
                ·
                  refine ⟨5177100919510595770965377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55222409808113021556964021 5177100919510595770965377)
                  ·
                    refine ⟨3882825689632946828224033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5177100919510595770965377 3882825689632946828224033)
                    ·
                      refine ⟨2912119267224710121168025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3882825689632946828224033 2912119267224710121168025)
                      ·
                        rfl

theorem cell23_5671332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_5671332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671332 prefixEnd_5671332 := by exact prefixLift 5671332
  have htrace : WordTrace (prefixWord ++ tailWord_5671332) baseStart_5671332 baseEnd_5671332 := by
    simpa [prefixWord, tailWord_5671332, baseEnd_5671332] using wordTrace_append hprefix tailTrace_5671332
  have hstable : (prefixWord ++ tailWord_5671332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671332).length < 2 ^ (prefixWord ++ tailWord_5671332).sum := by decide
  have hdescent : baseEnd_5671332 < baseStart_5671332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671335 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_5671335 : Nat := 118140960795 + 5671335 * 2 ^ 59
def prefixEnd_5671335 : Nat := 4983230072969 + 3 ^ 40 * 5671335 * 2
def baseEnd_5671335 : Nat := 2912120807666673609430511

theorem tailTrace_5671335 : CollatzResearch.WordTrace tailWord_5671335 prefixEnd_5671335 2912120807666673609430511 := by
  unfold tailWord_5671335
  simp only [CollatzResearch.WordTrace]
  refine ⟨206850580908729356749967459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137900387272486237833311639 206850580908729356749967459)
  ·
    refine ⟨310275871363094035124951189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206850580908729356749967459 310275871363094035124951189)
    ·
      refine ⟨14544181470145032896482087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 310275871363094035124951189 14544181470145032896482087)
      ·
        refine ⟨21816272205217549344723131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14544181470145032896482087 21816272205217549344723131)
        ·
          refine ⟨32724408307826324017084697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21816272205217549344723131 32724408307826324017084697)
          ·
            refine ⟨24543306230869743012813523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32724408307826324017084697 24543306230869743012813523)
            ·
              refine ⟨36814959346304614519220285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24543306230869743012813523 36814959346304614519220285)
              ·
                refine ⟨13805609754864230444707607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36814959346304614519220285 13805609754864230444707607)
                ·
                  refine ⟨20708414632296345667061411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13805609754864230444707607 20708414632296345667061411)
                  ·
                    refine ⟨31062621948444518500592117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20708414632296345667061411 31062621948444518500592117)
                    ·
                      refine ⟨2912120807666673609430511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31062621948444518500592117 2912120807666673609430511)
                      ·
                        rfl

theorem cell23_5671335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_5671335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671335 prefixEnd_5671335 := by exact prefixLift 5671335
  have htrace : WordTrace (prefixWord ++ tailWord_5671335) baseStart_5671335 baseEnd_5671335 := by
    simpa [prefixWord, tailWord_5671335, baseEnd_5671335] using wordTrace_append hprefix tailTrace_5671335
  have hstable : (prefixWord ++ tailWord_5671335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671335).length < 2 ^ (prefixWord ++ tailWord_5671335).sum := by decide
  have hdescent : baseEnd_5671335 < baseStart_5671335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671399 : List Nat := [1, 1, 5, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_5671399 : Nat := 118140960795 + 5671399 * 2 ^ 59
def prefixEnd_5671399 : Nat := 4983230072969 + 3 ^ 40 * 5671399 * 2
def baseEnd_5671399 : Nat := 2912153670428561359030217

theorem tailTrace_5671399 : CollatzResearch.WordTrace tailWord_5671399 prefixEnd_5671399 2912153670428561359030217 := by
  unfold tailWord_5671399
  simp only [CollatzResearch.WordTrace]
  refine ⟨206852915180497495680297251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137901943453664997120198167 206852915180497495680297251)
  ·
    refine ⟨310279372770746243520445877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206852915180497495680297251 310279372770746243520445877)
    ·
      refine ⟨29088691197257460330041801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 310279372770746243520445877 29088691197257460330041801)
      ·
        refine ⟨21816518397943095247531351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29088691197257460330041801 21816518397943095247531351)
        ·
          refine ⟨32724777596914642871297027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21816518397943095247531351 32724777596914642871297027)
          ·
            refine ⟨49087166395371964306945541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32724777596914642871297027 49087166395371964306945541)
            ·
              refine ⟨9203843699132243307552289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49087166395371964306945541 9203843699132243307552289)
              ·
                refine ⟨6902882774349182480664217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9203843699132243307552289 6902882774349182480664217)
                ·
                  refine ⟨5177162080761886860498163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6902882774349182480664217 5177162080761886860498163)
                  ·
                    refine ⟨7765743121142830290747245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5177162080761886860498163 7765743121142830290747245)
                    ·
                      refine ⟨2912153670428561359030217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7765743121142830290747245 2912153670428561359030217)
                      ·
                        rfl

theorem cell23_5671399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_5671399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671399 prefixEnd_5671399 := by exact prefixLift 5671399
  have htrace : WordTrace (prefixWord ++ tailWord_5671399) baseStart_5671399 baseEnd_5671399 := by
    simpa [prefixWord, tailWord_5671399, baseEnd_5671399] using wordTrace_append hprefix tailTrace_5671399
  have hstable : (prefixWord ++ tailWord_5671399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671399).length < 2 ^ (prefixWord ++ tailWord_5671399).sum := by decide
  have hdescent : baseEnd_5671399 < baseStart_5671399 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671456 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 4, 2, 2]
def baseStart_5671456 : Nat := 118140960795 + 5671456 * 2 ^ 59
def prefixEnd_5671456 : Nat := 4983230072969 + 3 ^ 40 * 5671456 * 2
def baseEnd_5671456 : Nat := 2912182938825867636017455

theorem tailTrace_5671456 : CollatzResearch.WordTrace tailWord_5671456 prefixEnd_5671456 2912182938825867636017455 := by
  unfold tailWord_5671456
  simp only [CollatzResearch.WordTrace]
  refine ⟨103427497070645497207561111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137903329427527329610081481 103427497070645497207561111)
  ·
    refine ⟨155141245605968245811341667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103427497070645497207561111 155141245605968245811341667)
    ·
      refine ⟨232711868408952368717012501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155141245605968245811341667 232711868408952368717012501)
      ·
        refine ⟨10908368831669642283609961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 232711868408952368717012501 10908368831669642283609961)
        ·
          refine ⟨8181276623752231712707471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10908368831669642283609961 8181276623752231712707471)
          ·
            refine ⟨12271914935628347569061207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8181276623752231712707471 12271914935628347569061207)
            ·
              refine ⟨18407872403442521353591811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12271914935628347569061207 18407872403442521353591811)
              ·
                refine ⟨27611808605163782030387717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18407872403442521353591811 27611808605163782030387717)
                ·
                  refine ⟨5177214113468209130697697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27611808605163782030387717 5177214113468209130697697)
                  ·
                    refine ⟨3882910585101156848023273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5177214113468209130697697 3882910585101156848023273)
                    ·
                      refine ⟨2912182938825867636017455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3882910585101156848023273 2912182938825867636017455)
                      ·
                        rfl

theorem cell23_5671456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_5671456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671456 prefixEnd_5671456 := by exact prefixLift 5671456
  have htrace : WordTrace (prefixWord ++ tailWord_5671456) baseStart_5671456 baseEnd_5671456 := by
    simpa [prefixWord, tailWord_5671456, baseEnd_5671456] using wordTrace_append hprefix tailTrace_5671456
  have hstable : (prefixWord ++ tailWord_5671456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671456).length < 2 ^ (prefixWord ++ tailWord_5671456).sum := by decide
  have hdescent : baseEnd_5671456 < baseStart_5671456 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671512 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 4, 4, 2]
def baseStart_5671512 : Nat := 118140960795 + 5671512 * 2 ^ 59
def prefixEnd_5671512 : Nat := 4983230072969 + 3 ^ 40 * 5671512 * 2
def baseEnd_5671512 : Nat := 2912211693742519416917197

theorem tailTrace_5671512 : CollatzResearch.WordTrace tailWord_5671512 prefixEnd_5671512 2912211693742519416917197 := by
  unfold tailWord_5671512
  simp only [CollatzResearch.WordTrace]
  refine ⟨103428518314544057989580395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137904691086058743986107193 103428518314544057989580395)
  ·
    refine ⟨155142777471816086984370593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103428518314544057989580395 155142777471816086984370593)
    ·
      refine ⟨116357083103862065238277945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155142777471816086984370593 116357083103862065238277945)
      ·
        refine ⟨87267812327896548928708459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116357083103862065238277945 87267812327896548928708459)
        ·
          refine ⟨130901718491844823393062689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87267812327896548928708459 130901718491844823393062689)
          ·
            refine ⟨98176288868883617544797017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130901718491844823393062689 98176288868883617544797017)
            ·
              refine ⟨73632216651662713158597763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98176288868883617544797017 73632216651662713158597763)
              ·
                refine ⟨110448324977494069737896645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73632216651662713158597763 110448324977494069737896645)
                ·
                  refine ⟨20709060933280138075855621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110448324977494069737896645 20709060933280138075855621)
                  ·
                    refine ⟨3882948924990025889222929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20709060933280138075855621 3882948924990025889222929)
                    ·
                      refine ⟨2912211693742519416917197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3882948924990025889222929 2912211693742519416917197)
                      ·
                        rfl

theorem cell23_5671512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4, 4, 2].length) (baseStart_5671512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671512 prefixEnd_5671512 := by exact prefixLift 5671512
  have htrace : WordTrace (prefixWord ++ tailWord_5671512) baseStart_5671512 baseEnd_5671512 := by
    simpa [prefixWord, tailWord_5671512, baseEnd_5671512] using wordTrace_append hprefix tailTrace_5671512
  have hstable : (prefixWord ++ tailWord_5671512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671512).length < 2 ^ (prefixWord ++ tailWord_5671512).sum := by decide
  have hdescent : baseEnd_5671512 < baseStart_5671512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671612 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 1, 6]
def baseStart_5671612 : Nat := 118140960795 + 5671612 * 2 ^ 59
def prefixEnd_5671612 : Nat := 4983230072969 + 3 ^ 40 * 5671612 * 2
def baseEnd_5671612 : Nat := 970754347269323008555579

theorem tailTrace_5671612 : CollatzResearch.WordTrace tailWord_5671612 prefixEnd_5671612 970754347269323008555579 := by
  unfold tailWord_5671612
  simp only [CollatzResearch.WordTrace]
  refine ⟨103430341964362916528900545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137907122619150555371867393 103430341964362916528900545)
  ·
    refine ⟨77572756473272187396675409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103430341964362916528900545 77572756473272187396675409)
    ·
      refine ⟨58179567354954140547506557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77572756473272187396675409 58179567354954140547506557)
      ·
        refine ⟨21817337758107802705314959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58179567354954140547506557 21817337758107802705314959)
        ·
          refine ⟨32726006637161704057972439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21817337758107802705314959 32726006637161704057972439)
          ·
            refine ⟨49089009955742556086958659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32726006637161704057972439 49089009955742556086958659)
            ·
              refine ⟨73633514933613834130437989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49089009955742556086958659 73633514933613834130437989)
              ·
                refine ⟨13806284050052593899457123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73633514933613834130437989 13806284050052593899457123)
                ·
                  refine ⟨20709426075078890849185685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13806284050052593899457123 20709426075078890849185685)
                  ·
                    refine ⟨970754347269323008555579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20709426075078890849185685 970754347269323008555579)
                    ·
                      rfl

theorem cell23_5671612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_5671612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671612 prefixEnd_5671612 := by exact prefixLift 5671612
  have htrace : WordTrace (prefixWord ++ tailWord_5671612) baseStart_5671612 baseEnd_5671612 := by
    simpa [prefixWord, tailWord_5671612, baseEnd_5671612] using wordTrace_append hprefix tailTrace_5671612
  have hstable : (prefixWord ++ tailWord_5671612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671612).length < 2 ^ (prefixWord ++ tailWord_5671612).sum := by decide
  have hdescent : baseEnd_5671612 < baseStart_5671612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671613 : List Nat := [1, 4, 1, 2, 1, 4, 2, 3, 1, 1, 3]
def baseStart_5671613 : Nat := 118140960795 + 5671613 * 2 ^ 59
def prefixEnd_5671613 : Nat := 4983230072969 + 3 ^ 40 * 5671613 * 2
def baseEnd_5671613 : Nat := 2912263555288623521754233

theorem tailTrace_5671613 : CollatzResearch.WordTrace tailWord_5671613 prefixEnd_5671613 2912263555288623521754233 := by
  unfold tailWord_5671613
  simp only [CollatzResearch.WordTrace]
  refine ⟨206860720401722210228587493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137907146934481473485724995 206860720401722210228587493)
  ·
    refine ⟨38786385075322914417860155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 206860720401722210228587493 38786385075322914417860155)
    ·
      refine ⟨58179577612984371626790233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38786385075322914417860155 58179577612984371626790233)
      ·
        refine ⟨43634683209738278720092675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58179577612984371626790233 43634683209738278720092675)
        ·
          refine ⟨65452024814607418080139013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43634683209738278720092675 65452024814607418080139013)
          ·
            refine ⟨12272254652738890890026065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65452024814607418080139013 12272254652738890890026065)
            ·
              refine ⟨9204190989554168167519549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12272254652738890890026065 9204190989554168167519549)
              ·
                refine ⟨3451571621082813062819831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9204190989554168167519549 3451571621082813062819831)
                ·
                  refine ⟨5177357431624219594229747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3451571621082813062819831 5177357431624219594229747)
                  ·
                    refine ⟨7766036147436329391344621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5177357431624219594229747 7766036147436329391344621)
                    ·
                      refine ⟨2912263555288623521754233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7766036147436329391344621 2912263555288623521754233)
                      ·
                        rfl

theorem cell23_5671613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_5671613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671613 prefixEnd_5671613 := by exact prefixLift 5671613
  have htrace : WordTrace (prefixWord ++ tailWord_5671613) baseStart_5671613 baseEnd_5671613 := by
    simpa [prefixWord, tailWord_5671613, baseEnd_5671613] using wordTrace_append hprefix tailTrace_5671613
  have hstable : (prefixWord ++ tailWord_5671613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671613).length < 2 ^ (prefixWord ++ tailWord_5671613).sum := by decide
  have hdescent : baseEnd_5671613 < baseStart_5671613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671616 : List Nat := [2, 1, 1, 2, 4, 4, 2, 1, 1, 5]
def baseStart_5671616 : Nat := 118140960795 + 5671616 * 2 ^ 59
def prefixEnd_5671616 : Nat := 4983230072969 + 3 ^ 40 * 5671616 * 2
def baseEnd_5671616 : Nat := 970755031910195670005573

theorem tailTrace_5671616 : CollatzResearch.WordTrace tailWord_5671616 prefixEnd_5671616 970755031910195670005573 := by
  unfold tailWord_5671616
  simp only [CollatzResearch.WordTrace]
  refine ⟨103430414910355670870473351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137907219880474227827297801 103430414910355670870473351)
  ·
    refine ⟨155145622365533506305710027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103430414910355670870473351 155145622365533506305710027)
    ·
      refine ⟨232718433548300259458565041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155145622365533506305710027 232718433548300259458565041)
      ·
        refine ⟨174538825161225194593923781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232718433548300259458565041 174538825161225194593923781)
        ·
          refine ⟨32726029717729723986360709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174538825161225194593923781 32726029717729723986360709)
          ·
            refine ⟨6136130572074323247442633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32726029717729723986360709 6136130572074323247442633)
            ·
              refine ⟨4602097929055742435581975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6136130572074323247442633 4602097929055742435581975)
              ·
                refine ⟨6903146893583613653372963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4602097929055742435581975 6903146893583613653372963)
                ·
                  refine ⟨10354720340375420480059445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6903146893583613653372963 10354720340375420480059445)
                  ·
                    refine ⟨970755031910195670005573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10354720340375420480059445 970755031910195670005573)
                    ·
                      rfl

theorem cell23_5671616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 1, 5].length) (baseStart_5671616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671616 prefixEnd_5671616 := by exact prefixLift 5671616
  have htrace : WordTrace (prefixWord ++ tailWord_5671616) baseStart_5671616 baseEnd_5671616 := by
    simpa [prefixWord, tailWord_5671616, baseEnd_5671616] using wordTrace_append hprefix tailTrace_5671616
  have hstable : (prefixWord ++ tailWord_5671616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671616).length < 2 ^ (prefixWord ++ tailWord_5671616).sum := by decide
  have hdescent : baseEnd_5671616 < baseStart_5671616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671649 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 1, 2, 4]
def baseStart_5671649 : Nat := 118140960795 + 5671649 * 2 ^ 59
def prefixEnd_5671649 : Nat := 4983230072969 + 3 ^ 40 * 5671649 * 2
def baseEnd_5671649 : Nat := 2912282040592185380904067

theorem tailTrace_5671649 : CollatzResearch.WordTrace tailWord_5671649 prefixEnd_5671649 2912282040592185380904067 := by
  unfold tailWord_5671649
  simp only [CollatzResearch.WordTrace]
  refine ⟨206862033429591788376898001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137908022286394525584598667 206862033429591788376898001)
  ·
    refine ⟨155146525072193841282673501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 206862033429591788376898001 155146525072193841282673501)
    ·
      refine ⟨58179946902072690481002563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155146525072193841282673501 58179946902072690481002563)
      ·
        refine ⟨87269920353109035721503845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58179946902072690481002563 87269920353109035721503845)
        ·
          refine ⟨16363110066207944197781971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87269920353109035721503845 16363110066207944197781971)
          ·
            refine ⟨24544665099311916296672957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16363110066207944197781971 24544665099311916296672957)
            ·
              refine ⟨9204249412241968611252359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24544665099311916296672957 9204249412241968611252359)
              ·
                refine ⟨13806374118362952916878539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9204249412241968611252359 13806374118362952916878539)
                ·
                  refine ⟨20709561177544429375317809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13806374118362952916878539 20709561177544429375317809)
                  ·
                    refine ⟨15532170883158322031488357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20709561177544429375317809 15532170883158322031488357)
                    ·
                      refine ⟨2912282040592185380904067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15532170883158322031488357 2912282040592185380904067)
                      ·
                        rfl

theorem cell23_5671649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_5671649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671649 prefixEnd_5671649 := by exact prefixLift 5671649
  have htrace : WordTrace (prefixWord ++ tailWord_5671649) baseStart_5671649 baseEnd_5671649 := by
    simpa [prefixWord, tailWord_5671649, baseEnd_5671649] using wordTrace_append hprefix tailTrace_5671649
  have hstable : (prefixWord ++ tailWord_5671649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671649).length < 2 ^ (prefixWord ++ tailWord_5671649).sum := by decide
  have hdescent : baseEnd_5671649 < baseStart_5671649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671679 : List Nat := [1, 1, 2, 2, 1, 3, 1, 2, 5, 3, 2]
def baseStart_5671679 : Nat := 118140960795 + 5671679 * 2 ^ 59
def prefixEnd_5671679 : Nat := 4983230072969 + 3 ^ 40 * 5671679 * 2
def baseEnd_5671679 : Nat := 2912297445011820263528929

theorem tailTrace_5671679 : CollatzResearch.WordTrace tailWord_5671679 prefixEnd_5671679 2912297445011820263528929 := by
  unfold tailWord_5671679
  simp only [CollatzResearch.WordTrace]
  refine ⟨206863127619483103500490091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137908751746322069000326727 206863127619483103500490091)
  ·
    refine ⟨310294691429224655250735137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206863127619483103500490091 310294691429224655250735137)
    ·
      refine ⟨232721018571918491438051353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310294691429224655250735137 232721018571918491438051353)
      ·
        refine ⟨174540763928938868578538515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232721018571918491438051353 174540763928938868578538515)
        ·
          refine ⟨261811145893408302867807773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174540763928938868578538515 261811145893408302867807773)
          ·
            refine ⟨98179179710028113575427915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261811145893408302867807773 98179179710028113575427915)
            ·
              refine ⟨147268769565042170363141873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98179179710028113575427915 147268769565042170363141873)
              ·
                refine ⟨110451577173781627772356405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147268769565042170363141873 110451577173781627772356405)
                ·
                  refine ⟨10354835360042027603658413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110451577173781627772356405 10354835360042027603658413)
                  ·
                    refine ⟨3883063260015760351371905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10354835360042027603658413 3883063260015760351371905)
                    ·
                      refine ⟨2912297445011820263528929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3883063260015760351371905 2912297445011820263528929)
                      ·
                        rfl

theorem cell23_5671679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 3, 2].length) (baseStart_5671679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671679 prefixEnd_5671679 := by exact prefixLift 5671679
  have htrace : WordTrace (prefixWord ++ tailWord_5671679) baseStart_5671679 baseEnd_5671679 := by
    simpa [prefixWord, tailWord_5671679, baseEnd_5671679] using wordTrace_append hprefix tailTrace_5671679
  have hstable : (prefixWord ++ tailWord_5671679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671679).length < 2 ^ (prefixWord ++ tailWord_5671679).sum := by decide
  have hdescent : baseEnd_5671679 < baseStart_5671679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671687 : List Nat := [1, 1, 4, 4, 1, 2, 3, 2, 1, 2, 2]
def baseStart_5671687 : Nat := 118140960795 + 5671687 * 2 ^ 59
def prefixEnd_5671687 : Nat := 4983230072969 + 3 ^ 40 * 5671687 * 2
def baseEnd_5671687 : Nat := 2912301552857056232228893

theorem tailTrace_5671687 : CollatzResearch.WordTrace tailWord_5671687 prefixEnd_5671687 2912301552857056232228893 := by
  unfold tailWord_5671687
  simp only [CollatzResearch.WordTrace]
  refine ⟨206863419403454120866781315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137908946268969413911187543 206863419403454120866781315)
  ·
    refine ⟨310295129105181181300171973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206863419403454120866781315 310295129105181181300171973)
    ·
      refine ⟨58180336707221471493782245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310295129105181181300171973 58180336707221471493782245)
      ·
        refine ⟨10908813132604025905084171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58180336707221471493782245 10908813132604025905084171)
        ·
          refine ⟨16363219698906038857626257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10908813132604025905084171 16363219698906038857626257)
          ·
            refine ⟨12272414774179529143219693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16363219698906038857626257 12272414774179529143219693)
            ·
              refine ⟨4602155540317323428707385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12272414774179529143219693 4602155540317323428707385)
              ·
                refine ⟨3451616655237992571530539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4602155540317323428707385 3451616655237992571530539)
                ·
                  refine ⟨5177424982856988857295809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3451616655237992571530539 5177424982856988857295809)
                  ·
                    refine ⟨3883068737142741642971857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5177424982856988857295809 3883068737142741642971857)
                    ·
                      refine ⟨2912301552857056232228893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3883068737142741642971857 2912301552857056232228893)
                      ·
                        rfl

theorem cell23_5671687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_5671687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671687 prefixEnd_5671687 := by exact prefixLift 5671687
  have htrace : WordTrace (prefixWord ++ tailWord_5671687) baseStart_5671687 baseEnd_5671687 := by
    simpa [prefixWord, tailWord_5671687, baseEnd_5671687] using wordTrace_append hprefix tailTrace_5671687
  have hstable : (prefixWord ++ tailWord_5671687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671687).length < 2 ^ (prefixWord ++ tailWord_5671687).sum := by decide
  have hdescent : baseEnd_5671687 < baseStart_5671687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671692 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 2, 3, 4]
def baseStart_5671692 : Nat := 118140960795 + 5671692 * 2 ^ 59
def prefixEnd_5671692 : Nat := 4983230072969 + 3 ^ 40 * 5671692 * 2
def baseEnd_5671692 : Nat := 2912304120260328712666369

theorem tailTrace_5671692 : CollatzResearch.WordTrace tailWord_5671692 prefixEnd_5671692 2912304120260328712666369 := by
  unfold tailWord_5671692
  simp only [CollatzResearch.WordTrace]
  refine ⟨103431800884218003360356665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137909067845624004480475553 103431800884218003360356665)
  ·
    refine ⟨77573850663163502520267499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103431800884218003360356665 77573850663163502520267499)
    ·
      refine ⟨116360775994745253780401249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77573850663163502520267499 116360775994745253780401249)
      ·
        refine ⟨87270581996058940335300937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116360775994745253780401249 87270581996058940335300937)
        ·
          refine ⟨65452936497044205251475703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87270581996058940335300937 65452936497044205251475703)
          ·
            refine ⟨98179404745566307877213555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65452936497044205251475703 98179404745566307877213555)
            ·
              refine ⟨147269107118349461815820333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98179404745566307877213555 147269107118349461815820333)
              ·
                refine ⟨55225915169381048180932625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147269107118349461815820333 55225915169381048180932625)
                ·
                  refine ⟨41419436377035786135699469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55225915169381048180932625 41419436377035786135699469)
                  ·
                    refine ⟨15532288641388419800887301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41419436377035786135699469 15532288641388419800887301)
                    ·
                      refine ⟨2912304120260328712666369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15532288641388419800887301 2912304120260328712666369)
                      ·
                        rfl

theorem cell23_5671692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_5671692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671692 prefixEnd_5671692 := by exact prefixLift 5671692
  have htrace : WordTrace (prefixWord ++ tailWord_5671692) baseStart_5671692 baseEnd_5671692 := by
    simpa [prefixWord, tailWord_5671692, baseEnd_5671692] using wordTrace_append hprefix tailTrace_5671692
  have hstable : (prefixWord ++ tailWord_5671692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671692).length < 2 ^ (prefixWord ++ tailWord_5671692).sum := by decide
  have hdescent : baseEnd_5671692 < baseStart_5671692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671703 : List Nat := [1, 1, 3, 4, 3, 1, 1, 3, 2, 1, 3]
def baseStart_5671703 : Nat := 118140960795 + 5671703 * 2 ^ 59
def prefixEnd_5671703 : Nat := 4983230072969 + 3 ^ 40 * 5671703 * 2
def baseEnd_5671703 : Nat := 2912309768547528169628819

theorem tailTrace_5671703 : CollatzResearch.WordTrace tailWord_5671703 prefixEnd_5671703 2912309768547528169628819 := by
  unfold tailWord_5671703
  simp only [CollatzResearch.WordTrace]
  refine ⟨206864002971396155599363763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137909335314264103732909175 206864002971396155599363763)
  ·
    refine ⟨310296004457094233399045645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206864002971396155599363763 310296004457094233399045645)
    ·
      refine ⟨116361001671410337524642117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310296004457094233399045645 116361001671410337524642117)
      ·
        refine ⟨21817687813389438285870397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116361001671410337524642117 21817687813389438285870397)
        ·
          refine ⟨8181632930021039357201399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21817687813389438285870397 8181632930021039357201399)
          ·
            refine ⟨12272449395031559035802099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8181632930021039357201399 12272449395031559035802099)
            ·
              refine ⟨18408674092547338553703149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12272449395031559035802099 18408674092547338553703149)
              ·
                refine ⟨6903252784705251957638681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18408674092547338553703149 6903252784705251957638681)
                ·
                  refine ⟨5177439588528938968229011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6903252784705251957638681 5177439588528938968229011)
                  ·
                    refine ⟨7766159382793408452343517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5177439588528938968229011 7766159382793408452343517)
                    ·
                      refine ⟨2912309768547528169628819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7766159382793408452343517 2912309768547528169628819)
                      ·
                        rfl

theorem cell23_5671703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_5671703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671703 prefixEnd_5671703 := by exact prefixLift 5671703
  have htrace : WordTrace (prefixWord ++ tailWord_5671703) baseStart_5671703 baseEnd_5671703 := by
    simpa [prefixWord, tailWord_5671703, baseEnd_5671703] using wordTrace_append hprefix tailTrace_5671703
  have hstable : (prefixWord ++ tailWord_5671703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671703).length < 2 ^ (prefixWord ++ tailWord_5671703).sum := by decide
  have hdescent : baseEnd_5671703 < baseStart_5671703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671743 : List Nat := [1, 1, 2, 2, 5, 1, 1, 4, 2, 2, 2]
def baseStart_5671743 : Nat := 118140960795 + 5671743 * 2 ^ 59
def prefixEnd_5671743 : Nat := 4983230072969 + 3 ^ 40 * 5671743 * 2
def baseEnd_5671743 : Nat := 2912330307773708013128635

theorem tailTrace_5671743 : CollatzResearch.WordTrace tailWord_5671743 prefixEnd_5671743 2912330307773708013128635 := by
  unfold tailWord_5671743
  simp only [CollatzResearch.WordTrace]
  refine ⟨206865461891251242430819883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137910307927500828287213255 206865461891251242430819883)
  ·
    refine ⟨310298192836876863646229825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206865461891251242430819883 310298192836876863646229825)
    ·
      refine ⟨232723644627657647734672369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310298192836876863646229825 232723644627657647734672369)
      ·
        refine ⟨174542733470743235801004277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232723644627657647734672369 174542733470743235801004277)
        ·
          refine ⟨16363381262882178356344151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174542733470743235801004277 16363381262882178356344151)
          ·
            refine ⟨24545071894323267534516227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16363381262882178356344151 24545071894323267534516227)
            ·
              refine ⟨36817607841484901301774341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24545071894323267534516227 36817607841484901301774341)
              ·
                refine ⟨6903301470278418994082689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36817607841484901301774341 6903301470278418994082689)
                ·
                  refine ⟨5177476102708814245562017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6903301470278418994082689 5177476102708814245562017)
                  ·
                    refine ⟨3883107077031610684171513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5177476102708814245562017 3883107077031610684171513)
                    ·
                      refine ⟨2912330307773708013128635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3883107077031610684171513 2912330307773708013128635)
                      ·
                        rfl

theorem cell23_5671743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 2, 2, 2].length) (baseStart_5671743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671743 prefixEnd_5671743 := by exact prefixLift 5671743
  have htrace : WordTrace (prefixWord ++ tailWord_5671743) baseStart_5671743 baseEnd_5671743 := by
    simpa [prefixWord, tailWord_5671743, baseEnd_5671743] using wordTrace_append hprefix tailTrace_5671743
  have hstable : (prefixWord ++ tailWord_5671743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671743).length < 2 ^ (prefixWord ++ tailWord_5671743).sum := by decide
  have hdescent : baseEnd_5671743 < baseStart_5671743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671779 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 1, 7]
def baseStart_5671779 : Nat := 118140960795 + 5671779 * 2 ^ 59
def prefixEnd_5671779 : Nat := 4983230072969 + 3 ^ 40 * 5671779 * 2
def baseEnd_5671779 : Nat := 970782931025756624092823

theorem tailTrace_5671779 : CollatzResearch.WordTrace tailWord_5671779 prefixEnd_5671779 970782931025756624092823 := by
  unfold tailWord_5671779
  simp only [CollatzResearch.WordTrace]
  refine ⟨206866774919120820579130391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137911183279413880386086927 206866774919120820579130391)
  ·
    refine ⟨310300162378681230868695587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206866774919120820579130391 310300162378681230868695587)
    ·
      refine ⟨465450243568021846303043381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310300162378681230868695587 465450243568021846303043381)
      ·
        refine ⟨43635960334502048090910317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 465450243568021846303043381 43635960334502048090910317)
        ·
          refine ⟨16363485125438268034091369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43635960334502048090910317 16363485125438268034091369)
          ·
            refine ⟨12272613844078701025568527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16363485125438268034091369 12272613844078701025568527)
            ·
              refine ⟨18408920766118051538352791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12272613844078701025568527 18408920766118051538352791)
              ·
                refine ⟨27613381149177077307529187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18408920766118051538352791 27613381149177077307529187)
                ·
                  refine ⟨41420071723765615961293781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27613381149177077307529187 41420071723765615961293781)
                  ·
                    refine ⟨970782931025756624092823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41420071723765615961293781 970782931025756624092823)
                    ·
                      rfl

theorem cell23_5671779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 7].length) (baseStart_5671779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671779 prefixEnd_5671779 := by exact prefixLift 5671779
  have htrace : WordTrace (prefixWord ++ tailWord_5671779) baseStart_5671779 baseEnd_5671779 := by
    simpa [prefixWord, tailWord_5671779, baseEnd_5671779] using wordTrace_append hprefix tailTrace_5671779
  have hstable : (prefixWord ++ tailWord_5671779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671779).length < 2 ^ (prefixWord ++ tailWord_5671779).sum := by decide
  have hdescent : baseEnd_5671779 < baseStart_5671779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671799 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 4]
def baseStart_5671799 : Nat := 118140960795 + 5671799 * 2 ^ 59
def prefixEnd_5671799 : Nat := 4983230072969 + 3 ^ 40 * 5671799 * 2
def baseEnd_5671799 : Nat := 2912359062690359794028377

theorem tailTrace_5671799 : CollatzResearch.WordTrace tailWord_5671799 prefixEnd_5671799 2912359062690359794028377 := by
  unfold tailWord_5671799
  simp only [CollatzResearch.WordTrace]
  refine ⟨206867504379048363994858451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137911669586032242663238967 206867504379048363994858451)
  ·
    refine ⟨310301256568572545992287677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206867504379048363994858451 310301256568572545992287677)
    ·
      refine ⟨116362971213214704747107879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310301256568572545992287677 116362971213214704747107879)
      ·
        refine ⟨174544456819822057120661819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116362971213214704747107879 174544456819822057120661819)
        ·
          refine ⟨261816685229733085680992729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174544456819822057120661819 261816685229733085680992729)
          ·
            refine ⟨196362513922299814260744547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261816685229733085680992729 196362513922299814260744547)
            ·
              refine ⟨294543770883449721391116821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196362513922299814260744547 294543770883449721391116821)
              ·
                refine ⟨13806739260161705690208601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 294543770883449721391116821 13806739260161705690208601)
                ·
                  refine ⟨10355054445121279267656451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13806739260161705690208601 10355054445121279267656451)
                  ·
                    refine ⟨15532581667681918901484677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10355054445121279267656451 15532581667681918901484677)
                    ·
                      refine ⟨2912359062690359794028377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15532581667681918901484677 2912359062690359794028377)
                      ·
                        rfl

theorem cell23_5671799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_5671799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671799 prefixEnd_5671799 := by exact prefixLift 5671799
  have htrace : WordTrace (prefixWord ++ tailWord_5671799) baseStart_5671799 baseEnd_5671799 := by
    simpa [prefixWord, tailWord_5671799, baseEnd_5671799] using wordTrace_append hprefix tailTrace_5671799
  have hstable : (prefixWord ++ tailWord_5671799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671799).length < 2 ^ (prefixWord ++ tailWord_5671799).sum := by decide
  have hdescent : baseEnd_5671799 < baseStart_5671799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671819 : List Nat := [1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 3]
def baseStart_5671819 : Nat := 118140960795 + 5671819 * 2 ^ 59
def prefixEnd_5671819 : Nat := 4983230072969 + 3 ^ 40 * 5671819 * 2
def baseEnd_5671819 : Nat := 2912369332303449715778285

theorem tailTrace_5671819 : CollatzResearch.WordTrace tailWord_5671819 prefixEnd_5671819 2912369332303449715778285 := by
  unfold tailWord_5671819
  simp only [CollatzResearch.WordTrace]
  refine ⟨206868233838975907410586511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137912155892650604940391007 206868233838975907410586511)
  ·
    refine ⟨310302350758463861115879767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206868233838975907410586511 310302350758463861115879767)
    ·
      refine ⟨465453526137695791673819651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310302350758463861115879767 465453526137695791673819651)
      ·
        refine ⟨698180289206543687510729477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465453526137695791673819651 698180289206543687510729477)
        ·
          refine ⟨130908804226226941408261777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 698180289206543687510729477 130908804226226941408261777)
          ·
            refine ⟨98181603169670206056196333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130908804226226941408261777 98181603169670206056196333)
            ·
              refine ⟨36818101188626327271073625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98181603169670206056196333 36818101188626327271073625)
              ·
                refine ⟨27613575891469745453305219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36818101188626327271073625 27613575891469745453305219)
                ·
                  refine ⟨41420363837204618179957829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27613575891469745453305219 41420363837204618179957829)
                  ·
                    refine ⟨7766318219475865908742093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41420363837204618179957829 7766318219475865908742093)
                    ·
                      refine ⟨2912369332303449715778285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7766318219475865908742093 2912369332303449715778285)
                      ·
                        rfl

theorem cell23_5671819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 4, 3].length) (baseStart_5671819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671819 prefixEnd_5671819 := by exact prefixLift 5671819
  have htrace : WordTrace (prefixWord ++ tailWord_5671819) baseStart_5671819 baseEnd_5671819 := by
    simpa [prefixWord, tailWord_5671819, baseEnd_5671819] using wordTrace_append hprefix tailTrace_5671819
  have hstable : (prefixWord ++ tailWord_5671819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671819).length < 2 ^ (prefixWord ++ tailWord_5671819).sum := by decide
  have hdescent : baseEnd_5671819 < baseStart_5671819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671839 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 8]
def baseStart_5671839 : Nat := 118140960795 + 5671839 * 2 ^ 59
def prefixEnd_5671839 : Nat := 4983230072969 + 3 ^ 40 * 5671839 * 2
def baseEnd_5671839 : Nat := 323597733546282181947577

theorem tailTrace_5671839 : CollatzResearch.WordTrace tailWord_5671839 prefixEnd_5671839 323597733546282181947577 := by
  unfold tailWord_5671839
  simp only [CollatzResearch.WordTrace]
  refine ⟨206868963298903450826314571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137912642199268967217543047 206868963298903450826314571)
  ·
    refine ⟨310303444948355176239471857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206868963298903450826314571 310303444948355176239471857)
    ·
      refine ⟨232727583711266382179603893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310303444948355176239471857 232727583711266382179603893)
      ·
        refine ⟨21818210972931223329337865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 232727583711266382179603893 21818210972931223329337865)
        ·
          refine ⟨16363658229698417497003399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21818210972931223329337865 16363658229698417497003399)
          ·
            refine ⟨24545487344547626245505099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16363658229698417497003399 24545487344547626245505099)
            ·
              refine ⟨36818231016821439368257649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24545487344547626245505099 36818231016821439368257649)
              ·
                refine ⟨27613673262616079526193237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36818231016821439368257649 27613673262616079526193237)
                ·
                  refine ⟨323597733546282181947577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27613673262616079526193237 323597733546282181947577)
                  ·
                    rfl

theorem cell23_5671839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 8].length) (baseStart_5671839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671839 prefixEnd_5671839 := by exact prefixLift 5671839
  have htrace : WordTrace (prefixWord ++ tailWord_5671839) baseStart_5671839 baseEnd_5671839 := by
    simpa [prefixWord, tailWord_5671839, baseEnd_5671839] using wordTrace_append hprefix tailTrace_5671839
  have hstable : (prefixWord ++ tailWord_5671839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671839).length < 2 ^ (prefixWord ++ tailWord_5671839).sum := by decide
  have hdescent : baseEnd_5671839 < baseStart_5671839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671843 : List Nat := [1, 1, 1, 4, 1, 2, 5, 3, 1, 4]
def baseStart_5671843 : Nat := 118140960795 + 5671843 * 2 ^ 59
def prefixEnd_5671843 : Nat := 4983230072969 + 3 ^ 40 * 5671843 * 2
def baseEnd_5671843 : Nat := 970793885279719207292725

theorem tailTrace_5671843 : CollatzResearch.WordTrace tailWord_5671843 prefixEnd_5671843 970793885279719207292725 := by
  unfold tailWord_5671843
  simp only [CollatzResearch.WordTrace]
  refine ⟨206869109190888959509460183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137912739460592639672973455 206869109190888959509460183)
  ·
    refine ⟨310303663786333439264190275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206869109190888959509460183 310303663786333439264190275)
    ·
      refine ⟨465455495679500158896285413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310303663786333439264190275 465455495679500158896285413)
      ·
        refine ⟨87272905439906279793053515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 465455495679500158896285413 87272905439906279793053515)
        ·
          refine ⟨130909358159859419689580273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87272905439906279793053515 130909358159859419689580273)
          ·
            refine ⟨98182018619894564767185205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130909358159859419689580273 98182018619894564767185205)
            ·
              refine ⟨9204564245615115446923613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98182018619894564767185205 9204564245615115446923613)
              ·
                refine ⟨3451711592105668292596355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9204564245615115446923613 3451711592105668292596355)
                ·
                  refine ⟨5177567388158502438894533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3451711592105668292596355 5177567388158502438894533)
                  ·
                    refine ⟨970793885279719207292725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5177567388158502438894533 970793885279719207292725)
                    ·
                      rfl

theorem cell23_5671843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 1, 4].length) (baseStart_5671843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671843 prefixEnd_5671843 := by exact prefixLift 5671843
  have htrace : WordTrace (prefixWord ++ tailWord_5671843) baseStart_5671843 baseEnd_5671843 := by
    simpa [prefixWord, tailWord_5671843, baseEnd_5671843] using wordTrace_append hprefix tailTrace_5671843
  have hstable : (prefixWord ++ tailWord_5671843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671843).length < 2 ^ (prefixWord ++ tailWord_5671843).sum := by decide
  have hdescent : baseEnd_5671843 < baseStart_5671843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671860 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_5671860 : Nat := 118140960795 + 5671860 * 2 ^ 59
def prefixEnd_5671860 : Nat := 4983230072969 + 3 ^ 40 * 5671860 * 2
def baseEnd_5671860 : Nat := 970796795003428018455199

theorem tailTrace_5671860 : CollatzResearch.WordTrace tailWord_5671860 prefixEnd_5671860 970796795003428018455199 := by
  unfold tailWord_5671860
  simp only [CollatzResearch.WordTrace]
  refine ⟨103434864615913685706414517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137913152821218247608552689 103434864615913685706414517)
  ·
    refine ⟨9697018557741908034976361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 103434864615913685706414517 9697018557741908034976361)
    ·
      refine ⟨7272763918306431026232271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9697018557741908034976361 7272763918306431026232271)
      ·
        refine ⟨10909145877459646539348407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7272763918306431026232271 10909145877459646539348407)
        ·
          refine ⟨16363718816189469809022611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10909145877459646539348407 16363718816189469809022611)
          ·
            refine ⟨24545578224284204713533917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16363718816189469809022611 24545578224284204713533917)
            ·
              refine ⟨9204591834106576767575219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24545578224284204713533917 9204591834106576767575219)
              ·
                refine ⟨13806887751159865151362829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9204591834106576767575219 13806887751159865151362829)
                ·
                  refine ⟨5177582906684949431761061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13806887751159865151362829 5177582906684949431761061)
                  ·
                    refine ⟨970796795003428018455199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5177582906684949431761061 970796795003428018455199)
                    ·
                      rfl

theorem cell23_5671860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_5671860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671860 prefixEnd_5671860 := by exact prefixLift 5671860
  have htrace : WordTrace (prefixWord ++ tailWord_5671860) baseStart_5671860 baseEnd_5671860 := by
    simpa [prefixWord, tailWord_5671860, baseEnd_5671860] using wordTrace_append hprefix tailTrace_5671860
  have hstable : (prefixWord ++ tailWord_5671860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671860).length < 2 ^ (prefixWord ++ tailWord_5671860).sum := by decide
  have hdescent : baseEnd_5671860 < baseStart_5671860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671886 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 3, 5]
def baseStart_5671886 : Nat := 118140960795 + 5671886 * 2 ^ 59
def prefixEnd_5671886 : Nat := 4983230072969 + 3 ^ 40 * 5671886 * 2
def baseEnd_5671886 : Nat := 970801245169100317880159

theorem tailTrace_5671886 : CollatzResearch.WordTrace tailWord_5671886 prefixEnd_5671886 970801245169100317880159 := by
  unfold tailWord_5671886
  simp only [CollatzResearch.WordTrace]
  refine ⟨25858834691216647231659439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 137913785019822118568850341 25858834691216647231659439)
  ·
    refine ⟨38788252036824970847489159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25858834691216647231659439 38788252036824970847489159)
    ·
      refine ⟨58182378055237456271233739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38788252036824970847489159 58182378055237456271233739)
      ·
        refine ⟨87273567082856184406850609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58182378055237456271233739 87273567082856184406850609)
        ·
          refine ⟨65455175312142138305137957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87273567082856184406850609 65455175312142138305137957)
          ·
            refine ⟨12272845371026650932213367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65455175312142138305137957 12272845371026650932213367)
            ·
              refine ⟨18409268056539976398320051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12272845371026650932213367 18409268056539976398320051)
              ·
                refine ⟨27613902084809964597480077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18409268056539976398320051 27613902084809964597480077)
                ·
                  refine ⟨10355213281803736724055029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27613902084809964597480077 10355213281803736724055029)
                  ·
                    refine ⟨970801245169100317880159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10355213281803736724055029 970801245169100317880159)
                    ·
                      rfl

theorem cell23_5671886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_5671886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671886 prefixEnd_5671886 := by exact prefixLift 5671886
  have htrace : WordTrace (prefixWord ++ tailWord_5671886) baseStart_5671886 baseEnd_5671886 := by
    simpa [prefixWord, tailWord_5671886, baseEnd_5671886] using wordTrace_append hprefix tailTrace_5671886
  have hstable : (prefixWord ++ tailWord_5671886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671886).length < 2 ^ (prefixWord ++ tailWord_5671886).sum := by decide
  have hdescent : baseEnd_5671886 < baseStart_5671886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671943 : List Nat := [1, 1, 4, 3, 1, 1, 2, 4, 1, 2, 3]
def baseStart_5671943 : Nat := 118140960795 + 5671943 * 2 ^ 59
def prefixEnd_5671943 : Nat := 4983230072969 + 3 ^ 40 * 5671943 * 2
def baseEnd_5671943 : Nat := 2912433003904607230627715

theorem tailTrace_5671943 : CollatzResearch.WordTrace tailWord_5671943 prefixEnd_5671943 2912433003904607230627715 := by
  unfold tailWord_5671943
  simp only [CollatzResearch.WordTrace]
  refine ⟨206872756490526676588100483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137915170993684451058733655 206872756490526676588100483)
  ·
    refine ⟨310309134735790014882150725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206872756490526676588100483 310309134735790014882150725)
    ·
      refine ⟨58182962762960627790403261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310309134735790014882150725 58182962762960627790403261)
      ·
        refine ⟨21818611036110235421401223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58182962762960627790403261 21818611036110235421401223)
        ·
          refine ⟨32727916554165353132101835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21818611036110235421401223 32727916554165353132101835)
          ·
            refine ⟨49091874831248029698152753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32727916554165353132101835 49091874831248029698152753)
            ·
              refine ⟨36818906123436022273614565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49091874831248029698152753 36818906123436022273614565)
              ·
                refine ⟨6903544898144254176302731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36818906123436022273614565 6903544898144254176302731)
                ·
                  refine ⟨10355317347216381264454097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6903544898144254176302731 10355317347216381264454097)
                  ·
                    refine ⟨7766488010412285948340573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10355317347216381264454097 7766488010412285948340573)
                    ·
                      refine ⟨2912433003904607230627715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7766488010412285948340573 2912433003904607230627715)
                      ·
                        rfl

theorem cell23_5671943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_5671943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671943 prefixEnd_5671943 := by exact prefixLift 5671943
  have htrace : WordTrace (prefixWord ++ tailWord_5671943) baseStart_5671943 baseEnd_5671943 := by
    simpa [prefixWord, tailWord_5671943, baseEnd_5671943] using wordTrace_append hprefix tailTrace_5671943
  have hstable : (prefixWord ++ tailWord_5671943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671943).length < 2 ^ (prefixWord ++ tailWord_5671943).sum := by decide
  have hdescent : baseEnd_5671943 < baseStart_5671943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671957 : List Nat := [1, 3, 2, 1, 4, 1, 1, 5, 1, 2, 2]
def baseStart_5671957 : Nat := 118140960795 + 5671957 * 2 ^ 59
def prefixEnd_5671957 : Nat := 4983230072969 + 3 ^ 40 * 5671957 * 2
def baseEnd_5671957 : Nat := 2912440192633770175852651

theorem tailTrace_5671957 : CollatzResearch.WordTrace tailWord_5671957 prefixEnd_5671957 2912440192633770175852651 := by
  unfold tailWord_5671957
  simp only [CollatzResearch.WordTrace]
  refine ⟨206873267112475956979110125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137915511408317304652740083 206873267112475956979110125)
  ·
    refine ⟨77577475167178483867166297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206873267112475956979110125 77577475167178483867166297)
    ·
      refine ⟨58183106375383862900374723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77577475167178483867166297 58183106375383862900374723)
      ·
        refine ⟨87274659563075794350562085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58183106375383862900374723 87274659563075794350562085)
        ·
          refine ⟨16363998668076711440730391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87274659563075794350562085 16363998668076711440730391)
          ·
            refine ⟨24545998002115067161095587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16363998668076711440730391 24545998002115067161095587)
            ·
              refine ⟨36818997003172600741643381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24545998002115067161095587 36818997003172600741643381)
              ·
                refine ⟨3451780969047431319529067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36818997003172600741643381 3451780969047431319529067)
                ·
                  refine ⟨5177671453571146979293601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3451780969047431319529067 5177671453571146979293601)
                  ·
                    refine ⟨3883253590178360234470201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5177671453571146979293601 3883253590178360234470201)
                    ·
                      refine ⟨2912440192633770175852651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3883253590178360234470201 2912440192633770175852651)
                      ·
                        rfl

theorem cell23_5671957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_5671957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671957 prefixEnd_5671957 := by exact prefixLift 5671957
  have htrace : WordTrace (prefixWord ++ tailWord_5671957) baseStart_5671957 baseEnd_5671957 := by
    simpa [prefixWord, tailWord_5671957, baseEnd_5671957] using wordTrace_append hprefix tailTrace_5671957
  have hstable : (prefixWord ++ tailWord_5671957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671957).length < 2 ^ (prefixWord ++ tailWord_5671957).sum := by decide
  have hdescent : baseEnd_5671957 < baseStart_5671957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671960 : List Nat := [2, 1, 2, 3, 2, 2, 4, 1, 1, 2, 3]
def baseStart_5671960 : Nat := 118140960795 + 5671960 * 2 ^ 59
def prefixEnd_5671960 : Nat := 4983230072969 + 3 ^ 40 * 5671960 * 2
def baseEnd_5671960 : Nat := 2912441733075733664115137

theorem tailTrace_5671960 : CollatzResearch.WordTrace tailWord_5671960 prefixEnd_5671960 2912441733075733664115137 := by
  unfold tailWord_5671960
  simp only [CollatzResearch.WordTrace]
  refine ⟨103436688265732544245734667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137915584354310058994312889 103436688265732544245734667)
  ·
    refine ⟨155155032398598816368602001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103436688265732544245734667 155155032398598816368602001)
    ·
      refine ⟨116366274298949112276451501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155155032398598816368602001 116366274298949112276451501)
      ·
        refine ⟨43637352862105917103669313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116366274298949112276451501 43637352862105917103669313)
        ·
          refine ⟨32728014646579437827751985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43637352862105917103669313 32728014646579437827751985)
          ·
            refine ⟨24546010984934578370813989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32728014646579437827751985 24546010984934578370813989)
            ·
              refine ⟨4602377059675233444527623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24546010984934578370813989 4602377059675233444527623)
              ·
                refine ⟨6903565589512850166791435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4602377059675233444527623 6903565589512850166791435)
                ·
                  refine ⟨10355348384269275250187153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6903565589512850166791435 10355348384269275250187153)
                  ·
                    refine ⟨7766511288201956437640365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10355348384269275250187153 7766511288201956437640365)
                    ·
                      refine ⟨2912441733075733664115137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7766511288201956437640365 2912441733075733664115137)
                      ·
                        rfl

theorem cell23_5671960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_5671960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671960 prefixEnd_5671960 := by exact prefixLift 5671960
  have htrace : WordTrace (prefixWord ++ tailWord_5671960) baseStart_5671960 baseEnd_5671960 := by
    simpa [prefixWord, tailWord_5671960, baseEnd_5671960] using wordTrace_append hprefix tailTrace_5671960
  have hstable : (prefixWord ++ tailWord_5671960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671960).length < 2 ^ (prefixWord ++ tailWord_5671960).sum := by decide
  have hdescent : baseEnd_5671960 < baseStart_5671960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671973 : List Nat := [1, 3, 1, 2, 2, 2, 3, 1, 4, 1, 3]
def baseStart_5671973 : Nat := 118140960795 + 5671973 * 2 ^ 59
def prefixEnd_5671973 : Nat := 4983230072969 + 3 ^ 40 * 5671973 * 2
def baseEnd_5671973 : Nat := 2912448408324242113252577

theorem tailTrace_5671973 : CollatzResearch.WordTrace tailWord_5671973 prefixEnd_5671973 2912448408324242113252577 := by
  unfold tailWord_5671973
  simp only [CollatzResearch.WordTrace]
  refine ⟨206873850680417991711692573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137915900453611994474461715 206873850680417991711692573)
  ·
    refine ⟨77577694005156746891884715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206873850680417991711692573 77577694005156746891884715)
    ·
      refine ⟨116366541007735120337827073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77577694005156746891884715 116366541007735120337827073)
      ·
        refine ⟨87274905755801340253370305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116366541007735120337827073 87274905755801340253370305)
        ·
          refine ⟨65456179316851005190027729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87274905755801340253370305 65456179316851005190027729)
          ·
            refine ⟨49092134487638253892520797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65456179316851005190027729 49092134487638253892520797)
            ·
              refine ⟨18409550432864345209695299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49092134487638253892520797 18409550432864345209695299)
              ·
                refine ⟨27614325649296517814542949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18409550432864345209695299 27614325649296517814542949)
                ·
                  refine ⟨5177686059243097090226803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27614325649296517814542949 5177686059243097090226803)
                  ·
                    refine ⟨7766529088864645635340205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5177686059243097090226803 7766529088864645635340205)
                    ·
                      refine ⟨2912448408324242113252577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7766529088864645635340205 2912448408324242113252577)
                      ·
                        rfl

theorem cell23_5671973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 4, 1, 3].length) (baseStart_5671973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671973 prefixEnd_5671973 := by exact prefixLift 5671973
  have htrace : WordTrace (prefixWord ++ tailWord_5671973) baseStart_5671973 baseEnd_5671973 := by
    simpa [prefixWord, tailWord_5671973, baseEnd_5671973] using wordTrace_append hprefix tailTrace_5671973
  have hstable : (prefixWord ++ tailWord_5671973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671973).length < 2 ^ (prefixWord ++ tailWord_5671973).sum := by decide
  have hdescent : baseEnd_5671973 < baseStart_5671973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5671990 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_5671990 : Nat := 118140960795 + 5671990 * 2 ^ 59
def prefixEnd_5671990 : Nat := 4983230072969 + 3 ^ 40 * 5671990 * 2
def baseEnd_5671990 : Nat := 2912457137495368546739999

theorem tailTrace_5671990 : CollatzResearch.WordTrace tailWord_5671990 prefixEnd_5671990 2912457137495368546739999 := by
  unfold tailWord_5671990
  simp only [CollatzResearch.WordTrace]
  refine ⟨12929654420084775225941339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 137916313814237602410040949 12929654420084775225941339)
  ·
    refine ⟨19394481630127162838912009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12929654420084775225941339 19394481630127162838912009)
    ·
      refine ⟨14545861222595372129184007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19394481630127162838912009 14545861222595372129184007)
      ·
        refine ⟨21818791833893058193776011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14545861222595372129184007 21818791833893058193776011)
        ·
          refine ⟨32728187750839587290664017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21818791833893058193776011 32728187750839587290664017)
          ·
            refine ⟨24546140813129690467998013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32728187750839587290664017 24546140813129690467998013)
            ·
              refine ⟨9204802804923633925499255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24546140813129690467998013 9204802804923633925499255)
              ·
                refine ⟨13807204207385450888248883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9204802804923633925499255 13807204207385450888248883)
                ·
                  refine ⟨20710806311078176332373325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13807204207385450888248883 20710806311078176332373325)
                  ·
                    refine ⟨7766552366654316124639997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20710806311078176332373325 7766552366654316124639997)
                    ·
                      refine ⟨2912457137495368546739999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7766552366654316124639997 2912457137495368546739999)
                      ·
                        rfl

theorem cell23_5671990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_5671990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5671990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5671990 prefixEnd_5671990 := by exact prefixLift 5671990
  have htrace : WordTrace (prefixWord ++ tailWord_5671990) baseStart_5671990 baseEnd_5671990 := by
    simpa [prefixWord, tailWord_5671990, baseEnd_5671990] using wordTrace_append hprefix tailTrace_5671990
  have hstable : (prefixWord ++ tailWord_5671990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5671990).length < 2 ^ (prefixWord ++ tailWord_5671990).sum := by decide
  have hdescent : baseEnd_5671990 < baseStart_5671990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5671990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672000 : List Nat := [2, 1, 1, 2, 2, 3, 4, 2, 1, 3, 2]
def baseStart_5672000 : Nat := 118140960795 + 5672000 * 2 ^ 59
def prefixEnd_5672000 : Nat := 4983230072969 + 3 ^ 40 * 5672000 * 2
def baseEnd_5672000 : Nat := 2912462272301913507614953

theorem tailTrace_5672000 : CollatzResearch.WordTrace tailWord_5672000 prefixEnd_5672000 2912462272301913507614953 := by
  unfold tailWord_5672000
  simp only [CollatzResearch.WordTrace]
  refine ⟨103437417725660087661462727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137916556967546783548616969 103437417725660087661462727)
  ·
    refine ⟨155156126588490131492194091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103437417725660087661462727 155156126588490131492194091)
    ·
      refine ⟨232734189882735197238291137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155156126588490131492194091 232734189882735197238291137)
      ·
        refine ⟨174550642412051397928718353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232734189882735197238291137 174550642412051397928718353)
        ·
          refine ⟨130912981809038548446538765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174550642412051397928718353 130912981809038548446538765)
          ·
            refine ⟨49092368178389455667452037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 130912981809038548446538765 49092368178389455667452037)
            ·
              refine ⟨9204819033448022937647257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49092368178389455667452037 9204819033448022937647257)
              ·
                refine ⟨6903614275086017203235443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9204819033448022937647257 6903614275086017203235443)
                ·
                  refine ⟨10355421412629025804853165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6903614275086017203235443 10355421412629025804853165)
                  ·
                    refine ⟨3883283029735884676819937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10355421412629025804853165 3883283029735884676819937)
                    ·
                      refine ⟨2912462272301913507614953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3883283029735884676819937 2912462272301913507614953)
                      ·
                        rfl

theorem cell23_5672000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 2, 1, 3, 2].length) (baseStart_5672000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672000 prefixEnd_5672000 := by exact prefixLift 5672000
  have htrace : WordTrace (prefixWord ++ tailWord_5672000) baseStart_5672000 baseEnd_5672000 := by
    simpa [prefixWord, tailWord_5672000, baseEnd_5672000] using wordTrace_append hprefix tailTrace_5672000
  have hstable : (prefixWord ++ tailWord_5672000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672000).length < 2 ^ (prefixWord ++ tailWord_5672000).sum := by decide
  have hdescent : baseEnd_5672000 < baseStart_5672000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672019 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 11]
def baseStart_5672019 : Nat := 118140960795 + 5672019 * 2 ^ 59
def prefixEnd_5672019 : Nat := 4983230072969 + 3 ^ 40 * 5672019 * 2
def baseEnd_5672019 : Nat := 323608003159372103697485

theorem tailTrace_5672019 : CollatzResearch.WordTrace tailWord_5672019 prefixEnd_5672019 323608003159372103697485 := by
  unfold tailWord_5672019
  simp only [CollatzResearch.WordTrace]
  refine ⟨206875528438251341567867111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137917018958834227711911407 206875528438251341567867111)
  ·
    refine ⟨310313292657377012351800667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206875528438251341567867111 310313292657377012351800667)
    ·
      refine ⟨465469938986065518527701001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310313292657377012351800667 465469938986065518527701001)
      ·
        refine ⟨349102454239549138895775751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465469938986065518527701001 349102454239549138895775751)
        ·
          refine ⟨523653681359323708343663627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349102454239549138895775751 523653681359323708343663627)
          ·
            refine ⟨785480522038985562515495441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523653681359323708343663627 785480522038985562515495441)
            ·
              refine ⟨589110391529239171886621581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785480522038985562515495441 589110391529239171886621581)
              ·
                refine ⟨220916396823464689457483093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 589110391529239171886621581 220916396823464689457483093)
                ·
                  refine ⟨323608003159372103697485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 220916396823464689457483093 323608003159372103697485)
                  ·
                    rfl

theorem cell23_5672019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 11].length) (baseStart_5672019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672019 prefixEnd_5672019 := by exact prefixLift 5672019
  have htrace : WordTrace (prefixWord ++ tailWord_5672019) baseStart_5672019 baseEnd_5672019 := by
    simpa [prefixWord, tailWord_5672019, baseEnd_5672019] using wordTrace_append hprefix tailTrace_5672019
  have hstable : (prefixWord ++ tailWord_5672019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672019).length < 2 ^ (prefixWord ++ tailWord_5672019).sum := by decide
  have hdescent : baseEnd_5672019 < baseStart_5672019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672026 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4]
def baseStart_5672026 : Nat := 118140960795 + 5672026 * 2 ^ 59
def prefixEnd_5672026 : Nat := 4983230072969 + 3 ^ 40 * 5672026 * 2
def baseEnd_5672026 : Nat := 2912475622798930405889833

theorem tailTrace_5672026 : CollatzResearch.WordTrace tailWord_5672026 prefixEnd_5672026 2912475622798930405889833 := by
  unfold tailWord_5672026
  simp only [CollatzResearch.WordTrace]
  refine ⟨51718945937306495440842983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137917189166150654508914621 51718945937306495440842983)
  ·
    refine ⟨77578418905959743161264475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51718945937306495440842983 77578418905959743161264475)
    ·
      refine ⟨116367628358939614741896713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77578418905959743161264475 116367628358939614741896713)
      ·
        refine ⟨87275721269204711056422535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116367628358939614741896713 87275721269204711056422535)
        ·
          refine ⟨130913581903807066584633803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87275721269204711056422535 130913581903807066584633803)
          ·
            refine ⟨196370372855710599876950705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130913581903807066584633803 196370372855710599876950705)
            ·
              refine ⟨147277779641782949907713029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196370372855710599876950705 147277779641782949907713029)
              ·
                refine ⟨27614583682834303107696193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147277779641782949907713029 27614583682834303107696193)
                ·
                  refine ⟨20710937762125727330772145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27614583682834303107696193 20710937762125727330772145)
                  ·
                    refine ⟨15533203321594295498079109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20710937762125727330772145 15533203321594295498079109)
                    ·
                      refine ⟨2912475622798930405889833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15533203321594295498079109 2912475622798930405889833)
                      ·
                        rfl

theorem cell23_5672026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_5672026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672026 prefixEnd_5672026 := by exact prefixLift 5672026
  have htrace : WordTrace (prefixWord ++ tailWord_5672026) baseStart_5672026 baseEnd_5672026 := by
    simpa [prefixWord, tailWord_5672026, baseEnd_5672026] using wordTrace_append hprefix tailTrace_5672026
  have hstable : (prefixWord ++ tailWord_5672026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672026).length < 2 ^ (prefixWord ++ tailWord_5672026).sum := by decide
  have hdescent : baseEnd_5672026 < baseStart_5672026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672087 : List Nat := [1, 1, 3, 3, 3, 3, 2, 2, 5]
def baseStart_5672087 : Nat := 118140960795 + 5672087 * 2 ^ 59
def prefixEnd_5672087 : Nat := 4983230072969 + 3 ^ 40 * 5672087 * 2
def baseEnd_5672087 : Nat := 323611882790983851914117

theorem tailTrace_5672087 : CollatzResearch.WordTrace tailWord_5672087 prefixEnd_5672087 323611882790983851914117 := by
  unfold tailWord_5672087
  simp only [CollatzResearch.WordTrace]
  refine ⟨206878008602004989181342515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137918672401336659454228343 206878008602004989181342515)
  ·
    refine ⟨310317012903007483772013773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206878008602004989181342515 310317012903007483772013773)
    ·
      refine ⟨116368879838627806414505165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310317012903007483772013773 116368879838627806414505165)
      ·
        refine ⟨43638329939485427405439437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116368879838627806414505165 43638329939485427405439437)
        ·
          refine ⟨16364373727307035277039789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43638329939485427405439437 16364373727307035277039789)
          ·
            refine ⟨6136640147740138228889921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16364373727307035277039789 6136640147740138228889921)
            ·
              refine ⟨4602480110805103671667441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6136640147740138228889921 4602480110805103671667441)
              ·
                refine ⟨3451860083103827753750581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4602480110805103671667441 3451860083103827753750581)
                ·
                  refine ⟨323611882790983851914117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3451860083103827753750581 323611882790983851914117)
                  ·
                    rfl

theorem cell23_5672087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 2, 5].length) (baseStart_5672087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672087 prefixEnd_5672087 := by exact prefixLift 5672087
  have htrace : WordTrace (prefixWord ++ tailWord_5672087) baseStart_5672087 baseEnd_5672087 := by
    simpa [prefixWord, tailWord_5672087, baseEnd_5672087] using wordTrace_append hprefix tailTrace_5672087
  have hstable : (prefixWord ++ tailWord_5672087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672087).length < 2 ^ (prefixWord ++ tailWord_5672087).sum := by decide
  have hdescent : baseEnd_5672087 < baseStart_5672087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672090 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2]
def baseStart_5672090 : Nat := 118140960795 + 5672090 * 2 ^ 59
def prefixEnd_5672090 : Nat := 4983230072969 + 3 ^ 40 * 5672090 * 2
def baseEnd_5672090 : Nat := 2912508485560818155489539

theorem tailTrace_5672090 : CollatzResearch.WordTrace tailWord_5672090 prefixEnd_5672090 2912508485560818155489539 := by
  unfold tailWord_5672090
  simp only [CollatzResearch.WordTrace]
  refine ⟨51719529505248530173425431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 137918745347329413795801149 51719529505248530173425431)
  ·
    refine ⟨77579294257872795260138147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51719529505248530173425431 77579294257872795260138147)
    ·
      refine ⟨116368941386809192890207221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77579294257872795260138147 116368941386809192890207221)
      ·
        refine ⟨10909588255013361833456927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116368941386809192890207221 10909588255013361833456927)
        ·
          refine ⟨16364382382520042750185391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10909588255013361833456927 16364382382520042750185391)
          ·
            refine ⟨24546573573780064125278087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16364382382520042750185391 24546573573780064125278087)
            ·
              refine ⟨36819860360670096187917131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24546573573780064125278087 36819860360670096187917131)
              ·
                refine ⟨55229790541005144281875697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36819860360670096187917131 55229790541005144281875697)
                ·
                  refine ⟨41422342905753858211406773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55229790541005144281875697 41422342905753858211406773)
                  ·
                    refine ⟨3883344647414424207319385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41422342905753858211406773 3883344647414424207319385)
                    ·
                      refine ⟨2912508485560818155489539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3883344647414424207319385 2912508485560818155489539)
                      ·
                        rfl

theorem cell23_5672090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_5672090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672090 prefixEnd_5672090 := by exact prefixLift 5672090
  have htrace : WordTrace (prefixWord ++ tailWord_5672090) baseStart_5672090 baseEnd_5672090 := by
    simpa [prefixWord, tailWord_5672090, baseEnd_5672090] using wordTrace_append hprefix tailTrace_5672090
  have hstable : (prefixWord ++ tailWord_5672090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672090).length < 2 ^ (prefixWord ++ tailWord_5672090).sum := by decide
  have hdescent : baseEnd_5672090 < baseStart_5672090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672123 : List Nat := [1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 3]
def baseStart_5672123 : Nat := 118140960795 + 5672123 * 2 ^ 59
def prefixEnd_5672123 : Nat := 4983230072969 + 3 ^ 40 * 5672123 * 2
def baseEnd_5672123 : Nat := 2912525430422416526376887

theorem tailTrace_5672123 : CollatzResearch.WordTrace tailWord_5672123 prefixEnd_5672123 2912525430422416526376887 := by
  unfold tailWord_5672123
  simp only [CollatzResearch.WordTrace]
  refine ⟨206879321629874567329653023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137919547753249711553102015 206879321629874567329653023)
  ·
    refine ⟨310318982444811850994479535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206879321629874567329653023 310318982444811850994479535)
    ·
      refine ⟨465478473667217776491719303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310318982444811850994479535 465478473667217776491719303)
      ·
        refine ⟨698217710500826664737578955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465478473667217776491719303 698217710500826664737578955)
        ·
          refine ⟨1047326565751239997106368433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 698217710500826664737578955 1047326565751239997106368433)
          ·
            refine ⟨785494924313429997829776325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1047326565751239997106368433 785494924313429997829776325)
            ·
              refine ⟨147280298308768124593083061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 785494924313429997829776325 147280298308768124593083061)
              ·
                refine ⟨13807527966447011680601537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147280298308768124593083061 13807527966447011680601537)
                ·
                  refine ⟨10355645974835258760451153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13807527966447011680601537 10355645974835258760451153)
                  ·
                    refine ⟨7766734481126444070338365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10355645974835258760451153 7766734481126444070338365)
                    ·
                      refine ⟨2912525430422416526376887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7766734481126444070338365 2912525430422416526376887)
                      ·
                        rfl

theorem cell23_5672123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 3].length) (baseStart_5672123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672123 prefixEnd_5672123 := by exact prefixLift 5672123
  have htrace : WordTrace (prefixWord ++ tailWord_5672123) baseStart_5672123 baseEnd_5672123 := by
    simpa [prefixWord, tailWord_5672123, baseEnd_5672123] using wordTrace_append hprefix tailTrace_5672123
  have hstable : (prefixWord ++ tailWord_5672123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672123).length < 2 ^ (prefixWord ++ tailWord_5672123).sum := by decide
  have hdescent : baseEnd_5672123 < baseStart_5672123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672160 : List Nat := [2, 1, 1, 3, 1, 5, 3, 1, 6]
def baseStart_5672160 : Nat := 118140960795 + 5672160 * 2 ^ 59
def prefixEnd_5672160 : Nat := 4983230072969 + 3 ^ 40 * 5672160 * 2
def baseEnd_5672160 : Nat := 323616047689625875734913

theorem tailTrace_5672160 : CollatzResearch.WordTrace tailWord_5672160 prefixEnd_5672160 323616047689625875734913 := by
  unfold tailWord_5672160
  simp only [CollatzResearch.WordTrace]
  refine ⟨103440335565370261324374967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137920447420493681765833289 103440335565370261324374967)
  ·
    refine ⟨155160503348055391986562451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103440335565370261324374967 155160503348055391986562451)
    ·
      refine ⟨232740755022083087979843677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155160503348055391986562451 232740755022083087979843677)
      ·
        refine ⟨87277783133281157992441379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 232740755022083087979843677 87277783133281157992441379)
        ·
          refine ⟨130916674699921736988662069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87277783133281157992441379 130916674699921736988662069)
          ·
            refine ⟨12273438253117662842687069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 130916674699921736988662069 12273438253117662842687069)
            ·
              refine ⟨4602539344919123566007651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12273438253117662842687069 4602539344919123566007651)
              ·
                refine ⟨6903809017378685349011477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4602539344919123566007651 6903809017378685349011477)
                ·
                  refine ⟨323616047689625875734913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6903809017378685349011477 323616047689625875734913)
                  ·
                    rfl

theorem cell23_5672160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 3, 1, 6].length) (baseStart_5672160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672160 prefixEnd_5672160 := by exact prefixLift 5672160
  have htrace : WordTrace (prefixWord ++ tailWord_5672160) baseStart_5672160 baseEnd_5672160 := by
    simpa [prefixWord, tailWord_5672160, baseEnd_5672160] using wordTrace_append hprefix tailTrace_5672160
  have hstable : (prefixWord ++ tailWord_5672160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672160).length < 2 ^ (prefixWord ++ tailWord_5672160).sum := by decide
  have hdescent : baseEnd_5672160 < baseStart_5672160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672213 : List Nat := [1, 3, 2, 1, 2, 1, 1, 1, 2, 6, 3]
def baseStart_5672213 : Nat := 118140960795 + 5672213 * 2 ^ 59
def prefixEnd_5672213 : Nat := 4983230072969 + 3 ^ 40 * 5672213 * 2
def baseEnd_5672213 : Nat := 2912571643681321174251473

theorem tailTrace_5672213 : CollatzResearch.WordTrace tailWord_5672213 prefixEnd_5672213 2912571643681321174251473 := by
  unfold tailWord_5672213
  simp only [CollatzResearch.WordTrace]
  refine ⟨206882604199548512700429293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137921736133032341800286195 206882604199548512700429293)
  ·
    refine ⟨77580976574830692262660985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 206882604199548512700429293 77580976574830692262660985)
    ·
      refine ⟨58185732431123019196995739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77580976574830692262660985 58185732431123019196995739)
      ·
        refine ⟨87278598646684528795493609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58185732431123019196995739 87278598646684528795493609)
        ·
          refine ⟨65458948985013396596620207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87278598646684528795493609 65458948985013396596620207)
          ·
            refine ⟨98188423477520094894930311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65458948985013396596620207 98188423477520094894930311)
            ·
              refine ⟨147282635216280142342395467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98188423477520094894930311 147282635216280142342395467)
              ·
                refine ⟨220923952824420213513593201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147282635216280142342395467 220923952824420213513593201)
                ·
                  refine ⟨165692964618315160135194901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 220923952824420213513593201 165692964618315160135194901)
                  ·
                    refine ⟨7766857716483523131337261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 165692964618315160135194901 7766857716483523131337261)
                    ·
                      refine ⟨2912571643681321174251473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7766857716483523131337261 2912571643681321174251473)
                      ·
                        rfl

theorem cell23_5672213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_5672213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672213 prefixEnd_5672213 := by exact prefixLift 5672213
  have htrace : WordTrace (prefixWord ++ tailWord_5672213) baseStart_5672213 baseEnd_5672213 := by
    simpa [prefixWord, tailWord_5672213, baseEnd_5672213] using wordTrace_append hprefix tailTrace_5672213
  have hstable : (prefixWord ++ tailWord_5672213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672213).length < 2 ^ (prefixWord ++ tailWord_5672213).sum := by decide
  have hdescent : baseEnd_5672213 < baseStart_5672213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672224 : List Nat := [2, 1, 1, 5, 4, 1, 1, 2, 1, 5]
def baseStart_5672224 : Nat := 118140960795 + 5672224 * 2 ^ 59
def prefixEnd_5672224 : Nat := 4983230072969 + 3 ^ 40 * 5672224 * 2
def baseEnd_5672224 : Nat := 970859097322840210404641

theorem tailTrace_5672224 : CollatzResearch.WordTrace tailWord_5672224 prefixEnd_5672224 970859097322840210404641 := by
  unfold tailWord_5672224
  simp only [CollatzResearch.WordTrace]
  refine ⟨103441502701254330789539863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 137922003601672441052719817 103441502701254330789539863)
  ·
    refine ⟨155162254051881496184309795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103441502701254330789539863 155162254051881496184309795)
    ·
      refine ⟨232743381077822244276464693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155162254051881496184309795 232743381077822244276464693)
      ·
        refine ⟨21819691976045835400918565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 232743381077822244276464693 21819691976045835400918565)
        ·
          refine ⟨4091192245508594137672231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21819691976045835400918565 4091192245508594137672231)
          ·
            refine ⟨6136788368262891206508347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4091192245508594137672231 6136788368262891206508347)
            ·
              refine ⟨9205182552394336809762521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6136788368262891206508347 9205182552394336809762521)
              ·
                refine ⟨6903886914295752607321891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9205182552394336809762521 6903886914295752607321891)
                ·
                  refine ⟨10355830371443628910982837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6903886914295752607321891 10355830371443628910982837)
                  ·
                    refine ⟨970859097322840210404641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10355830371443628910982837 970859097322840210404641)
                    ·
                      rfl

theorem cell23_5672224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 1, 5].length) (baseStart_5672224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672224 prefixEnd_5672224 := by exact prefixLift 5672224
  have htrace : WordTrace (prefixWord ++ tailWord_5672224) baseStart_5672224 baseEnd_5672224 := by
    simpa [prefixWord, tailWord_5672224, baseEnd_5672224] using wordTrace_append hprefix tailTrace_5672224
  have hstable : (prefixWord ++ tailWord_5672224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672224).length < 2 ^ (prefixWord ++ tailWord_5672224).sum := by decide
  have hdescent : baseEnd_5672224 < baseStart_5672224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672227 : List Nat := [1, 1, 1, 4, 2, 5, 1, 2, 1, 1, 4]
def baseStart_5672227 : Nat := 118140960795 + 5672227 * 2 ^ 59
def prefixEnd_5672227 : Nat := 4983230072969 + 3 ^ 40 * 5672227 * 2
def baseEnd_5672227 : Nat := 2912578832410484119476409

theorem tailTrace_5672227 : CollatzResearch.WordTrace tailWord_5672227 prefixEnd_5672227 2912578832410484119476409 := by
  unfold tailWord_5672227
  simp only [CollatzResearch.WordTrace]
  refine ⟨206883114821497793091438935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137922076547665195394292623 206883114821497793091438935)
  ·
    refine ⟨310324672232246689637158403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206883114821497793091438935 310324672232246689637158403)
    ·
      refine ⟨465487008348370034455737605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 310324672232246689637158403 465487008348370034455737605)
      ·
        refine ⟨87278814065319381460450801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 465487008348370034455737605 87278814065319381460450801)
        ·
          refine ⟨65459110548989536095338101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87278814065319381460450801 65459110548989536095338101)
          ·
            refine ⟨6136791613967769008937947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65459110548989536095338101 6136791613967769008937947)
            ·
              refine ⟨9205187420951653513406921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6136791613967769008937947 9205187420951653513406921)
              ·
                refine ⟨6903890565713740135055191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9205187420951653513406921 6903890565713740135055191)
                ·
                  refine ⟨10355835848570610202582787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6903890565713740135055191 10355835848570610202582787)
                  ·
                    refine ⟨15533753772855915303874181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10355835848570610202582787 15533753772855915303874181)
                    ·
                      refine ⟨2912578832410484119476409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15533753772855915303874181 2912578832410484119476409)
                      ·
                        rfl

theorem cell23_5672227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_5672227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672227 prefixEnd_5672227 := by exact prefixLift 5672227
  have htrace : WordTrace (prefixWord ++ tailWord_5672227) baseStart_5672227 baseEnd_5672227 := by
    simpa [prefixWord, tailWord_5672227, baseEnd_5672227] using wordTrace_append hprefix tailTrace_5672227
  have hstable : (prefixWord ++ tailWord_5672227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672227).length < 2 ^ (prefixWord ++ tailWord_5672227).sum := by decide
  have hdescent : baseEnd_5672227 < baseStart_5672227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5672237 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 1, 6]
def baseStart_5672237 : Nat := 118140960795 + 5672237 * 2 ^ 59
def prefixEnd_5672237 : Nat := 4983230072969 + 3 ^ 40 * 5672237 * 2
def baseEnd_5672237 : Nat := 970861322405676360117121

theorem tailTrace_5672237 : CollatzResearch.WordTrace tailWord_5672237 prefixEnd_5672237 970861322405676360117121 := by
  unfold tailWord_5672237
  simp only [CollatzResearch.WordTrace]
  refine ⟨206883479551461564799302965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 137922319700974376532868643 206883479551461564799302965)
  ·
    refine ⟨19395326207949521699934653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 206883479551461564799302965 19395326207949521699934653)
    ·
      refine ⟨7273247327981070637475495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19395326207949521699934653 7273247327981070637475495)
      ·
        refine ⟨10909870991971605956213243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7273247327981070637475495 10909870991971605956213243)
        ·
          refine ⟨16364806487957408934319865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10909870991971605956213243 16364806487957408934319865)
          ·
            refine ⟨12273604865968056700739899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16364806487957408934319865 12273604865968056700739899)
            ·
              refine ⟨18410407298952085051109849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12273604865968056700739899 18410407298952085051109849)
              ·
                refine ⟨13807805474214063788332387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18410407298952085051109849 13807805474214063788332387)
                ·
                  refine ⟨20711708211321095682498581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13807805474214063788332387 20711708211321095682498581)
                  ·
                    refine ⟨970861322405676360117121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20711708211321095682498581 970861322405676360117121)
                    ·
                      rfl

theorem cell23_5672237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_5672237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5672237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5672237 prefixEnd_5672237 := by exact prefixLift 5672237
  have htrace : WordTrace (prefixWord ++ tailWord_5672237) baseStart_5672237 baseEnd_5672237 := by
    simpa [prefixWord, tailWord_5672237, baseEnd_5672237] using wordTrace_append hprefix tailTrace_5672237
  have hstable : (prefixWord ++ tailWord_5672237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5672237).length < 2 ^ (prefixWord ++ tailWord_5672237).sum := by decide
  have hdescent : baseEnd_5672237 < baseStart_5672237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5672237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
