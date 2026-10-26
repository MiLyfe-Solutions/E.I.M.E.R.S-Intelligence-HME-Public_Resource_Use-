import V185TrunkScan23Chunk0057

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_342868 : List Nat := [2, 4, 1, 1, 4, 1, 3, 1, 6]
def baseStart_342868 : Nat := 118140960795 + 342868 * 2 ^ 59
def prefixEnd_342868 : Nat := 4983230072969 + 3 ^ 40 * 342868 * 2
def baseEnd_342868 : Nat := 19561787227318862341465

theorem tailTrace_342868 : CollatzResearch.WordTrace tailWord_342868 prefixEnd_342868 19561787227318862341465 := by
  unfold tailWord_342868
  simp only [CollatzResearch.WordTrace]
  refine ⟨6252711660927634018766629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8336948881236845358355505 6252711660927634018766629)
  ·
    refine ⟨1172383436423931378518743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6252711660927634018766629 1172383436423931378518743)
    ·
      refine ⟨1758575154635897067778115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1172383436423931378518743 1758575154635897067778115)
      ·
        refine ⟨2637862731953845601667173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1758575154635897067778115 2637862731953845601667173)
        ·
          refine ⟨494599262241346050312595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2637862731953845601667173 494599262241346050312595)
          ·
            refine ⟨741898893362019075468893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494599262241346050312595 741898893362019075468893)
            ·
              refine ⟨278212085010757153300835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 741898893362019075468893 278212085010757153300835)
              ·
                refine ⟨417318127516135729951253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278212085010757153300835 417318127516135729951253)
                ·
                  refine ⟨19561787227318862341465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 417318127516135729951253 19561787227318862341465)
                  ·
                    rfl

theorem cell23_342868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_342868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342868 prefixEnd_342868 := by exact prefixLift 342868
  have htrace : WordTrace (prefixWord ++ tailWord_342868) baseStart_342868 baseEnd_342868 := by
    simpa [prefixWord, tailWord_342868, baseEnd_342868] using wordTrace_append hprefix tailTrace_342868
  have hstable : (prefixWord ++ tailWord_342868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342868).length < 2 ^ (prefixWord ++ tailWord_342868).sum := by decide
  have hdescent : baseEnd_342868 < baseStart_342868 := by decide
  rcases family_descends (prefixWord ++ tailWord_342868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342871 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 1, 5, 2]
def baseStart_342871 : Nat := 118140960795 + 342871 * 2 ^ 59
def prefixEnd_342871 : Nat := 4983230072969 + 3 ^ 40 * 342871 * 2
def baseEnd_342871 : Nat := 176057625487833249335671

theorem tailTrace_342871 : CollatzResearch.WordTrace tailWord_342871 prefixEnd_342871 176057625487833249335671 := by
  unfold tailWord_342871
  simp only [CollatzResearch.WordTrace]
  refine ⟨12505532740844399549892467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8337021827229599699928311 12505532740844399549892467)
  ·
    refine ⟨18758299111266599324838701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12505532740844399549892467 18758299111266599324838701)
    ·
      refine ⟨7034362166724974746814513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18758299111266599324838701 7034362166724974746814513)
      ·
        refine ⟨5275771625043731060110885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7034362166724974746814513 5275771625043731060110885)
        ·
          refine ⟨989207179695699573770791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5275771625043731060110885 989207179695699573770791)
          ·
            refine ⟨1483810769543549360656187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989207179695699573770791 1483810769543549360656187)
            ·
              refine ⟨2225716154315324040984281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1483810769543549360656187 2225716154315324040984281)
              ·
                refine ⟨1669287115736493030738211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2225716154315324040984281 1669287115736493030738211)
                ·
                  refine ⟨2503930673604739546107317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669287115736493030738211 2503930673604739546107317)
                  ·
                    refine ⟨234743500650444332447561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2503930673604739546107317 234743500650444332447561)
                    ·
                      refine ⟨176057625487833249335671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 234743500650444332447561 176057625487833249335671)
                      ·
                        rfl

theorem cell23_342871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 5, 2].length) (baseStart_342871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342871 prefixEnd_342871 := by exact prefixLift 342871
  have htrace : WordTrace (prefixWord ++ tailWord_342871) baseStart_342871 baseEnd_342871 := by
    simpa [prefixWord, tailWord_342871, baseEnd_342871] using wordTrace_append hprefix tailTrace_342871
  have hstable : (prefixWord ++ tailWord_342871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342871).length < 2 ^ (prefixWord ++ tailWord_342871).sum := by decide
  have hdescent : baseEnd_342871 < baseStart_342871 := by decide
  rcases family_descends (prefixWord ++ tailWord_342871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342907 : List Nat := [1, 1, 1, 1, 1, 5, 13]
def baseStart_342907 : Nat := 118140960795 + 342907 * 2 ^ 59
def prefixEnd_342907 : Nat := 4983230072969 + 3 ^ 40 * 342907 * 2
def baseEnd_342907 : Nat := 2173779145572779117105

theorem tailTrace_342907 : CollatzResearch.WordTrace tailWord_342907 prefixEnd_342907 2173779145572779117105 := by
  unfold tailWord_342907
  simp only [CollatzResearch.WordTrace]
  refine ⟨12506845768713977698202975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8337897179142651798801983 12506845768713977698202975)
  ·
    refine ⟨18760268653070966547304463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12506845768713977698202975 18760268653070966547304463)
    ·
      refine ⟨28140402979606449820956695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18760268653070966547304463 28140402979606449820956695)
      ·
        refine ⟨42210604469409674731435043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28140402979606449820956695 42210604469409674731435043)
        ·
          refine ⟨63315906704114512097152565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42210604469409674731435043 63315906704114512097152565)
          ·
            refine ⟨5935866253510735509108053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63315906704114512097152565 5935866253510735509108053)
            ·
              refine ⟨2173779145572779117105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 5935866253510735509108053 2173779145572779117105)
              ·
                rfl

theorem cell23_342907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 13].length) (baseStart_342907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342907 prefixEnd_342907 := by exact prefixLift 342907
  have htrace : WordTrace (prefixWord ++ tailWord_342907) baseStart_342907 baseEnd_342907 := by
    simpa [prefixWord, tailWord_342907, baseEnd_342907] using wordTrace_append hprefix tailTrace_342907
  have hstable : (prefixWord ++ tailWord_342907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342907).length < 2 ^ (prefixWord ++ tailWord_342907).sum := by decide
  have hdescent : baseEnd_342907 < baseStart_342907 := by decide
  rcases family_descends (prefixWord ++ tailWord_342907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342938 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3]
def baseStart_342938 : Nat := 118140960795 + 342938 * 2 ^ 59
def prefixEnd_342938 : Nat := 4983230072969 + 3 ^ 40 * 342938 * 2
def baseEnd_342938 : Nat := 176092028691684487197863

theorem tailTrace_342938 : CollatzResearch.WordTrace tailWord_342938 prefixEnd_342938 176092028691684487197863 := by
  unfold tailWord_342938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3126994107900417498145367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8338650954401113328387645 3126994107900417498145367)
  ·
    refine ⟨4690491161850626247218051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3126994107900417498145367 4690491161850626247218051)
    ·
      refine ⟨7035736742775939370827077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4690491161850626247218051 7035736742775939370827077)
      ·
        refine ⟨1319200639270488632030077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7035736742775939370827077 1319200639270488632030077)
        ·
          refine ⟨494700239726433237011279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1319200639270488632030077 494700239726433237011279)
          ·
            refine ⟨742050359589649855516919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494700239726433237011279 742050359589649855516919)
            ·
              refine ⟨1113075539384474783275379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742050359589649855516919 1113075539384474783275379)
              ·
                refine ⟨1669613309076712174913069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1113075539384474783275379 1669613309076712174913069)
                ·
                  refine ⟨626104990903767065592401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1669613309076712174913069 626104990903767065592401)
                  ·
                    refine ⟨469578743177825299194301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 626104990903767065592401 469578743177825299194301)
                    ·
                      refine ⟨176092028691684487197863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 469578743177825299194301 176092028691684487197863)
                      ·
                        rfl

theorem cell23_342938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_342938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342938 prefixEnd_342938 := by exact prefixLift 342938
  have htrace : WordTrace (prefixWord ++ tailWord_342938) baseStart_342938 baseEnd_342938 := by
    simpa [prefixWord, tailWord_342938, baseEnd_342938] using wordTrace_append hprefix tailTrace_342938
  have hstable : (prefixWord ++ tailWord_342938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342938).length < 2 ^ (prefixWord ++ tailWord_342938).sum := by decide
  have hdescent : baseEnd_342938 < baseStart_342938 := by decide
  rcases family_descends (prefixWord ++ tailWord_342938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342968 : List Nat := [2, 1, 2, 1, 2, 4, 1, 4, 2, 1, 3]
def baseStart_342968 : Nat := 118140960795 + 342968 * 2 ^ 59
def prefixEnd_342968 : Nat := 4983230072969 + 3 ^ 40 * 342968 * 2
def baseEnd_342968 : Nat := 176107433111319369822725

theorem tailTrace_342968 : CollatzResearch.WordTrace tailWord_342968 prefixEnd_342968 176107433111319369822725 := by
  unfold tailWord_342968
  simp only [CollatzResearch.WordTrace]
  refine ⟨6254535310746492558086779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8339380414328656744115705 6254535310746492558086779)
  ·
    refine ⟨9381802966119738837130169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6254535310746492558086779 9381802966119738837130169)
    ·
      refine ⟨7036352224589804127847627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9381802966119738837130169 7036352224589804127847627)
      ·
        refine ⟨10554528336884706191771441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7036352224589804127847627 10554528336884706191771441)
        ·
          refine ⟨7915896252663529643828581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10554528336884706191771441 7915896252663529643828581)
          ·
            refine ⟨1484230547374411808217859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7915896252663529643828581 1484230547374411808217859)
            ·
              refine ⟨2226345821061617712326789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484230547374411808217859 2226345821061617712326789)
              ·
                refine ⟨417439841449053321061273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2226345821061617712326789 417439841449053321061273)
                ·
                  refine ⟨313079881086789990795955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417439841449053321061273 313079881086789990795955)
                  ·
                    refine ⟨469619821630184986193933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 313079881086789990795955 469619821630184986193933)
                    ·
                      refine ⟨176107433111319369822725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 469619821630184986193933 176107433111319369822725)
                      ·
                        rfl

theorem cell23_342968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_342968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342968 prefixEnd_342968 := by exact prefixLift 342968
  have htrace : WordTrace (prefixWord ++ tailWord_342968) baseStart_342968 baseEnd_342968 := by
    simpa [prefixWord, tailWord_342968, baseEnd_342968] using wordTrace_append hprefix tailTrace_342968
  have hstable : (prefixWord ++ tailWord_342968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342968).length < 2 ^ (prefixWord ++ tailWord_342968).sum := by decide
  have hdescent : baseEnd_342968 < baseStart_342968 := by decide
  rcases family_descends (prefixWord ++ tailWord_342968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342969 : List Nat := [1, 2, 1, 4, 2, 4, 2, 2, 1, 2, 2]
def baseStart_342969 : Nat := 118140960795 + 342969 * 2 ^ 59
def prefixEnd_342969 : Nat := 4983230072969 + 3 ^ 40 * 342969 * 2
def baseEnd_342969 : Nat := 176107946591973865910221

theorem tailTrace_342969 : CollatzResearch.WordTrace tailWord_342969 prefixEnd_342969 176107946591973865910221 := by
  unfold tailWord_342969
  simp only [CollatzResearch.WordTrace]
  refine ⟨12509107094489362286959961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8339404729659574857973307 12509107094489362286959961)
  ·
    refine ⟨9381830320867021715219971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12509107094489362286959961 9381830320867021715219971)
    ·
      refine ⟨14072745481300532572829957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9381830320867021715219971 14072745481300532572829957)
      ·
        refine ⟨2638639777743849857405617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14072745481300532572829957 2638639777743849857405617)
        ·
          refine ⟨1978979833307887393054213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2638639777743849857405617 1978979833307887393054213)
          ·
            refine ⟨371058718745228886197665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1978979833307887393054213 371058718745228886197665)
            ·
              refine ⟨278294039058921664648249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371058718745228886197665 278294039058921664648249)
              ·
                refine ⟨208720529294191248486187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278294039058921664648249 208720529294191248486187)
                ·
                  refine ⟨313080793941286872729281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208720529294191248486187 313080793941286872729281)
                  ·
                    refine ⟨234810595455965154546961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 313080793941286872729281 234810595455965154546961)
                    ·
                      refine ⟨176107946591973865910221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 234810595455965154546961 176107946591973865910221)
                      ·
                        rfl

theorem cell23_342969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_342969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_342969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_342969 prefixEnd_342969 := by exact prefixLift 342969
  have htrace : WordTrace (prefixWord ++ tailWord_342969) baseStart_342969 baseEnd_342969 := by
    simpa [prefixWord, tailWord_342969, baseEnd_342969] using wordTrace_append hprefix tailTrace_342969
  have hstable : (prefixWord ++ tailWord_342969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342969).length < 2 ^ (prefixWord ++ tailWord_342969).sum := by decide
  have hdescent : baseEnd_342969 < baseStart_342969 := by decide
  rcases family_descends (prefixWord ++ tailWord_342969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343025 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 4, 2, 2]
def baseStart_343025 : Nat := 118140960795 + 343025 * 2 ^ 59
def prefixEnd_343025 : Nat := 4983230072969 + 3 ^ 40 * 343025 * 2
def baseEnd_343025 : Nat := 176136701508625646809963

theorem tailTrace_343025 : CollatzResearch.WordTrace tailWord_343025 prefixEnd_343025 176136701508625646809963 := by
  unfold tailWord_343025
  simp only [CollatzResearch.WordTrace]
  refine ⟨12511149582286483850998529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8340766388190989233999019 12511149582286483850998529)
  ·
    refine ⟨9383362186714862888248897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12511149582286483850998529 9383362186714862888248897)
    ·
      refine ⟨7037521640036147166186673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9383362186714862888248897 7037521640036147166186673)
      ·
        refine ⟨5278141230027110374640005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7037521640036147166186673 5278141230027110374640005)
        ·
          refine ⟨989651480630083195245001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5278141230027110374640005 989651480630083195245001)
          ·
            refine ⟨742238610472562396433751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 989651480630083195245001 742238610472562396433751)
            ·
              refine ⟨1113357915708843594650627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742238610472562396433751 1113357915708843594650627)
              ·
                refine ⟨1670036873563265391975941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1113357915708843594650627 1670036873563265391975941)
                ·
                  refine ⟨313131913793112260995489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1670036873563265391975941 313131913793112260995489)
                  ·
                    refine ⟨234848935344834195746617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 313131913793112260995489 234848935344834195746617)
                    ·
                      refine ⟨176136701508625646809963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 234848935344834195746617 176136701508625646809963)
                      ·
                        rfl

theorem cell23_343025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_343025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343025 prefixEnd_343025 := by exact prefixLift 343025
  have htrace : WordTrace (prefixWord ++ tailWord_343025) baseStart_343025 baseEnd_343025 := by
    simpa [prefixWord, tailWord_343025, baseEnd_343025] using wordTrace_append hprefix tailTrace_343025
  have hstable : (prefixWord ++ tailWord_343025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343025).length < 2 ^ (prefixWord ++ tailWord_343025).sum := by decide
  have hdescent : baseEnd_343025 < baseStart_343025 := by decide
  rcases family_descends (prefixWord ++ tailWord_343025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343061 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 1, 7]
def baseStart_343061 : Nat := 118140960795 + 343061 * 2 ^ 59
def prefixEnd_343061 : Nat := 4983230072969 + 3 ^ 40 * 343061 * 2
def baseEnd_343061 : Nat := 58718395604062501986599

theorem tailTrace_343061 : CollatzResearch.WordTrace tailWord_343061 prefixEnd_343061 58718395604062501986599 := by
  unfold tailWord_343061
  simp only [CollatzResearch.WordTrace]
  refine ⟨12512462610156061999309037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8341641740104041332872691 12512462610156061999309037)
  ·
    refine ⟨4692173478808523249740889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12512462610156061999309037 4692173478808523249740889)
    ·
      refine ⟨3519130109106392437305667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4692173478808523249740889 3519130109106392437305667)
      ·
        refine ⟨5278695163659588655958501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3519130109106392437305667 5278695163659588655958501)
        ·
          refine ⟨989755343186172872992219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5278695163659588655958501 989755343186172872992219)
          ·
            refine ⟨1484633014779259309488329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989755343186172872992219 1484633014779259309488329)
            ·
              refine ⟨1113474761084444482116247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1484633014779259309488329 1113474761084444482116247)
              ·
                refine ⟨1670212141626666723174371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1113474761084444482116247 1670212141626666723174371)
                ·
                  refine ⟨2505318212440000084761557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1670212141626666723174371 2505318212440000084761557)
                  ·
                    refine ⟨58718395604062501986599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2505318212440000084761557 58718395604062501986599)
                    ·
                      rfl

theorem cell23_343061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_343061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343061 prefixEnd_343061 := by exact prefixLift 343061
  have htrace : WordTrace (prefixWord ++ tailWord_343061) baseStart_343061 baseEnd_343061 := by
    simpa [prefixWord, tailWord_343061, baseEnd_343061] using wordTrace_append hprefix tailTrace_343061
  have hstable : (prefixWord ++ tailWord_343061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343061).length < 2 ^ (prefixWord ++ tailWord_343061).sum := by decide
  have hdescent : baseEnd_343061 < baseStart_343061 := by decide
  rcases family_descends (prefixWord ++ tailWord_343061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343082 : List Nat := [3, 1, 4, 1, 3, 1, 3, 2, 5]
def baseStart_343082 : Nat := 118140960795 + 343082 * 2 ^ 59
def prefixEnd_343082 : Nat := 4983230072969 + 3 ^ 40 * 343082 * 2
def baseEnd_343082 : Nat := 19573996656214658199689

theorem tailTrace_343082 : CollatzResearch.WordTrace tailWord_343082 prefixEnd_343082 19573996656214658199689 := by
  unfold tailWord_343082
  simp only [CollatzResearch.WordTrace]
  refine ⟨3128307135769995646455875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8342152362053321723882333 3128307135769995646455875)
  ·
    refine ⟨4692460703654993469683813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3128307135769995646455875 4692460703654993469683813)
    ·
      refine ⟨879836381935311275565715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4692460703654993469683813 879836381935311275565715)
      ·
        refine ⟨1319754572902966913348573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 879836381935311275565715 1319754572902966913348573)
        ·
          refine ⟨494907964838612592505715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1319754572902966913348573 494907964838612592505715)
          ·
            refine ⟨742361947257918888758573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494907964838612592505715 742361947257918888758573)
            ·
              refine ⟨278385730221719583284465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 742361947257918888758573 278385730221719583284465)
              ·
                refine ⟨208789297666289687463349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278385730221719583284465 208789297666289687463349)
                ·
                  refine ⟨19573996656214658199689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 208789297666289687463349 19573996656214658199689)
                  ·
                    rfl

theorem cell23_343082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 2, 5].length) (baseStart_343082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343082 prefixEnd_343082 := by exact prefixLift 343082
  have htrace : WordTrace (prefixWord ++ tailWord_343082) baseStart_343082 baseEnd_343082 := by
    simpa [prefixWord, tailWord_343082, baseEnd_343082] using wordTrace_append hprefix tailTrace_343082
  have hstable : (prefixWord ++ tailWord_343082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343082).length < 2 ^ (prefixWord ++ tailWord_343082).sum := by decide
  have hdescent : baseEnd_343082 < baseStart_343082 := by decide
  rcases family_descends (prefixWord ++ tailWord_343082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343098 : List Nat := [3, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2]
def baseStart_343098 : Nat := 118140960795 + 343098 * 2 ^ 59
def prefixEnd_343098 : Nat := 4983230072969 + 3 ^ 40 * 343098 * 2
def baseEnd_343098 : Nat := 176174185596403861197127

theorem tailTrace_343098 : CollatzResearch.WordTrace tailWord_343098 prefixEnd_343098 176174185596403861197127 := by
  unfold tailWord_343098
  simp only [CollatzResearch.WordTrace]
  refine ⟨3128453027755504329601487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8342541407348011545603965 3128453027755504329601487)
  ·
    refine ⟨4692679541633256494402231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3128453027755504329601487 4692679541633256494402231)
    ·
      refine ⟨7039019312449884741603347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4692679541633256494402231 7039019312449884741603347)
      ·
        refine ⟨10558528968674827112405021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7039019312449884741603347 10558528968674827112405021)
        ·
          refine ⟨3959448363253060167151883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10558528968674827112405021 3959448363253060167151883)
          ·
            refine ⟨5939172544879590250727825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3959448363253060167151883 5939172544879590250727825)
            ·
              refine ⟨4454379408659692688045869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5939172544879590250727825 4454379408659692688045869)
              ·
                refine ⟨1670392278247384758017201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4454379408659692688045869 1670392278247384758017201)
                ·
                  refine ⟨1252794208685538568512901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1670392278247384758017201 1252794208685538568512901)
                  ·
                    refine ⟨234898914128538481596169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1252794208685538568512901 234898914128538481596169)
                    ·
                      refine ⟨176174185596403861197127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 234898914128538481596169 176174185596403861197127)
                      ·
                        rfl

theorem cell23_343098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 3, 2, 4, 2].length) (baseStart_343098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343098 prefixEnd_343098 := by exact prefixLift 343098
  have htrace : WordTrace (prefixWord ++ tailWord_343098) baseStart_343098 baseEnd_343098 := by
    simpa [prefixWord, tailWord_343098, baseEnd_343098] using wordTrace_append hprefix tailTrace_343098
  have hstable : (prefixWord ++ tailWord_343098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343098).length < 2 ^ (prefixWord ++ tailWord_343098).sum := by decide
  have hdescent : baseEnd_343098 < baseStart_343098 := by decide
  rcases family_descends (prefixWord ++ tailWord_343098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343125 : List Nat := [1, 3, 2, 2, 1, 2, 2, 5, 1, 4]
def baseStart_343125 : Nat := 118140960795 + 343125 * 2 ^ 59
def prefixEnd_343125 : Nat := 4983230072969 + 3 ^ 40 * 343125 * 2
def baseEnd_343125 : Nat := 58729349858025085186501

theorem tailTrace_343125 : CollatzResearch.WordTrace tailWord_343125 prefixEnd_343125 58729349858025085186501 := by
  unfold tailWord_343125
  simp only [CollatzResearch.WordTrace]
  refine ⟨12514796881924200929638829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8343197921282800619759219 12514796881924200929638829)
  ·
    refine ⟨4693048830721575348614561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12514796881924200929638829 4693048830721575348614561)
    ·
      refine ⟨3519786623041181511460921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4693048830721575348614561 3519786623041181511460921)
      ·
        refine ⟨2639839967280886133595691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3519786623041181511460921 2639839967280886133595691)
        ·
          refine ⟨3959759950921329200393537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2639839967280886133595691 3959759950921329200393537)
          ·
            refine ⟨2969819963190996900295153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3959759950921329200393537 2969819963190996900295153)
            ·
              refine ⟨2227364972393247675221365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2969819963190996900295153 2227364972393247675221365)
              ·
                refine ⟨208815466161866969552003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2227364972393247675221365 208815466161866969552003)
                ·
                  refine ⟨313223199242800454328005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208815466161866969552003 313223199242800454328005)
                  ·
                    refine ⟨58729349858025085186501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 313223199242800454328005 58729349858025085186501)
                    ·
                      rfl

theorem cell23_343125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_343125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343125 prefixEnd_343125 := by exact prefixLift 343125
  have htrace : WordTrace (prefixWord ++ tailWord_343125) baseStart_343125 baseEnd_343125 := by
    simpa [prefixWord, tailWord_343125, baseEnd_343125] using wordTrace_append hprefix tailTrace_343125
  have hstable : (prefixWord ++ tailWord_343125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343125).length < 2 ^ (prefixWord ++ tailWord_343125).sum := by decide
  have hdescent : baseEnd_343125 < baseStart_343125 := by decide
  rcases family_descends (prefixWord ++ tailWord_343125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343141 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 1, 2, 6]
def baseStart_343141 : Nat := 118140960795 + 343141 * 2 ^ 59
def prefixEnd_343141 : Nat := 4983230072969 + 3 ^ 40 * 343141 * 2
def baseEnd_343141 : Nat := 176196265264547192959429

theorem tailTrace_343141 : CollatzResearch.WordTrace tailWord_343141 prefixEnd_343141 176196265264547192959429 := by
  unfold tailWord_343141
  simp only [CollatzResearch.WordTrace]
  refine ⟨12515380449866235662221277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8343586966577490441480851 12515380449866235662221277)
  ·
    refine ⟨4693267668699838373332979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12515380449866235662221277 4693267668699838373332979)
    ·
      refine ⟨7039901503049757559999469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4693267668699838373332979 7039901503049757559999469)
      ·
        refine ⟨2639963063643659084999801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7039901503049757559999469 2639963063643659084999801)
        ·
          refine ⟨1979972297732744313749851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2639963063643659084999801 1979972297732744313749851)
          ·
            refine ⟨2969958446599116470624777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1979972297732744313749851 2969958446599116470624777)
            ·
              refine ⟨2227468834949337352968583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2969958446599116470624777 2227468834949337352968583)
              ·
                refine ⟨3341203252424006029452875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227468834949337352968583 3341203252424006029452875)
                ·
                  refine ⟨5011804878636009044179313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3341203252424006029452875 5011804878636009044179313)
                  ·
                    refine ⟨3758853658977006783134485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5011804878636009044179313 3758853658977006783134485)
                    ·
                      refine ⟨176196265264547192959429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3758853658977006783134485 176196265264547192959429)
                      ·
                        rfl

theorem cell23_343141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_343141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343141 prefixEnd_343141 := by exact prefixLift 343141
  have htrace : WordTrace (prefixWord ++ tailWord_343141) baseStart_343141 baseEnd_343141 := by
    simpa [prefixWord, tailWord_343141, baseEnd_343141] using wordTrace_append hprefix tailTrace_343141
  have hstable : (prefixWord ++ tailWord_343141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343141).length < 2 ^ (prefixWord ++ tailWord_343141).sum := by decide
  have hdescent : baseEnd_343141 < baseStart_343141 := by decide
  rcases family_descends (prefixWord ++ tailWord_343141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343151 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 5, 5]
def baseStart_343151 : Nat := 118140960795 + 343151 * 2 ^ 59
def prefixEnd_343151 : Nat := 4983230072969 + 3 ^ 40 * 343151 * 2
def baseEnd_343151 : Nat := 58733800023697384611461

theorem tailTrace_343151 : CollatzResearch.WordTrace tailWord_343151 prefixEnd_343151 58733800023697384611461 := by
  unfold tailWord_343151
  simp only [CollatzResearch.WordTrace]
  refine ⟨12515745179830007370085307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8343830119886671580056871 12515745179830007370085307)
  ·
    refine ⟨18773617769745011055127961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12515745179830007370085307 18773617769745011055127961)
    ·
      refine ⟨14080213327308758291345971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18773617769745011055127961 14080213327308758291345971)
      ·
        refine ⟨21120319990963137437018957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14080213327308758291345971 21120319990963137437018957)
        ·
          refine ⟨7920119996611176538882109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21120319990963137437018957 7920119996611176538882109)
          ·
            refine ⟨2970044998729191202080791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7920119996611176538882109 2970044998729191202080791)
            ·
              refine ⟨4455067498093786803121187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2970044998729191202080791 4455067498093786803121187)
              ·
                refine ⟨6682601247140680204681781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4455067498093786803121187 6682601247140680204681781)
                ·
                  refine ⟨626493866919438769188917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6682601247140680204681781 626493866919438769188917)
                  ·
                    refine ⟨58733800023697384611461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 626493866919438769188917 58733800023697384611461)
                    ·
                      rfl

theorem cell23_343151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 5, 5].length) (baseStart_343151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343151 prefixEnd_343151 := by exact prefixLift 343151
  have htrace : WordTrace (prefixWord ++ tailWord_343151) baseStart_343151 baseEnd_343151 := by
    simpa [prefixWord, tailWord_343151, baseEnd_343151] using wordTrace_append hprefix tailTrace_343151
  have hstable : (prefixWord ++ tailWord_343151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343151).length < 2 ^ (prefixWord ++ tailWord_343151).sum := by decide
  have hdescent : baseEnd_343151 < baseStart_343151 := by decide
  rcases family_descends (prefixWord ++ tailWord_343151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343165 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 3, 1, 3]
def baseStart_343165 : Nat := 118140960795 + 343165 * 2 ^ 59
def prefixEnd_343165 : Nat := 4983230072969 + 3 ^ 40 * 343165 * 2
def baseEnd_343165 : Nat := 176208588800255099059319

theorem tailTrace_343165 : CollatzResearch.WordTrace tailWord_343165 prefixEnd_343165 176208588800255099059319 := by
  unfold tailWord_343165
  simp only [CollatzResearch.WordTrace]
  refine ⟨12516255801779287761094949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8344170534519525174063299 12516255801779287761094949)
  ·
    refine ⟨2346797962833616455205303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12516255801779287761094949 2346797962833616455205303)
    ·
      refine ⟨3520196944250424682807955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2346797962833616455205303 3520196944250424682807955)
      ·
        refine ⟨5280295416375637024211933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520196944250424682807955 5280295416375637024211933)
        ·
          refine ⟨1980110781140863884079475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5280295416375637024211933 1980110781140863884079475)
          ·
            refine ⟨2970166171711295826119213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1980110781140863884079475 2970166171711295826119213)
            ·
              refine ⟨1113812314391735934794705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2970166171711295826119213 1113812314391735934794705)
              ·
                refine ⟨835359235793801951096029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1113812314391735934794705 835359235793801951096029)
                ·
                  refine ⟨313259713422675731661011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 835359235793801951096029 313259713422675731661011)
                  ·
                    refine ⟨469889570134013597491517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 313259713422675731661011 469889570134013597491517)
                    ·
                      refine ⟨176208588800255099059319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 469889570134013597491517 176208588800255099059319)
                      ·
                        rfl

theorem cell23_343165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_343165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343165 prefixEnd_343165 := by exact prefixLift 343165
  have htrace : WordTrace (prefixWord ++ tailWord_343165) baseStart_343165 baseEnd_343165 := by
    simpa [prefixWord, tailWord_343165, baseEnd_343165] using wordTrace_append hprefix tailTrace_343165
  have hstable : (prefixWord ++ tailWord_343165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343165).length < 2 ^ (prefixWord ++ tailWord_343165).sum := by decide
  have hdescent : baseEnd_343165 < baseStart_343165 := by decide
  rcases family_descends (prefixWord ++ tailWord_343165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343166 : List Nat := [4, 2, 4, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_343166 : Nat := 118140960795 + 343166 * 2 ^ 59
def prefixEnd_343166 : Nat := 4983230072969 + 3 ^ 40 * 343166 * 2
def baseEnd_343166 : Nat := 176209102280909595146815

theorem tailTrace_343166 : CollatzResearch.WordTrace tailWord_343166 prefixEnd_343166 176209102280909595146815 := by
  unfold tailWord_343166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1564536534346958116485169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8344194849850443287920901 1564536534346958116485169)
  ·
    refine ⟨1173402400760218587363877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1564536534346958116485169 1173402400760218587363877)
    ·
      refine ⟨220012950142540985130727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1173402400760218587363877 220012950142540985130727)
      ·
        refine ⟨330019425213811477696091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220012950142540985130727 330019425213811477696091)
        ·
          refine ⟨495029137820717216544137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330019425213811477696091 495029137820717216544137)
          ·
            refine ⟨371271853365537912408103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 495029137820717216544137 371271853365537912408103)
            ·
              refine ⟨556907780048306868612155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371271853365537912408103 556907780048306868612155)
              ·
                refine ⟨835361670072460302918233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556907780048306868612155 835361670072460302918233)
                ·
                  refine ⟨626521252554345227188675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 835361670072460302918233 626521252554345227188675)
                  ·
                    refine ⟨939781878831517840783013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 626521252554345227188675 939781878831517840783013)
                    ·
                      refine ⟨176209102280909595146815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 939781878831517840783013 176209102280909595146815)
                      ·
                        rfl

theorem cell23_343166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_343166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343166 prefixEnd_343166 := by exact prefixLift 343166
  have htrace : WordTrace (prefixWord ++ tailWord_343166) baseStart_343166 baseEnd_343166 := by
    simpa [prefixWord, tailWord_343166, baseEnd_343166] using wordTrace_append hprefix tailTrace_343166
  have hstable : (prefixWord ++ tailWord_343166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343166).length < 2 ^ (prefixWord ++ tailWord_343166).sum := by decide
  have hdescent : baseEnd_343166 < baseStart_343166 := by decide
  rcases family_descends (prefixWord ++ tailWord_343166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343218 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_343218 : Nat := 118140960795 + 343218 * 2 ^ 59
def prefixEnd_343218 : Nat := 4983230072969 + 3 ^ 40 * 343218 * 2
def baseEnd_343218 : Nat := 176235803274943391696575

theorem tailTrace_343218 : CollatzResearch.WordTrace tailWord_343218 prefixEnd_343218 176235803274943391696575 := by
  unfold tailWord_343218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3129547217646819453193577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8345459247058185208516205 3129547217646819453193577)
  ·
    refine ⟨2347160413235114589895183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3129547217646819453193577 2347160413235114589895183)
    ·
      refine ⟨3520740619852671884842775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2347160413235114589895183 3520740619852671884842775)
      ·
        refine ⟨5281110929779007827264163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520740619852671884842775 5281110929779007827264163)
        ·
          refine ⟨7921666394668511740896245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5281110929779007827264163 7921666394668511740896245)
          ·
            refine ⟨742656224500172975709023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7921666394668511740896245 742656224500172975709023)
            ·
              refine ⟨1113984336750259463563535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742656224500172975709023 1113984336750259463563535)
              ·
                refine ⟨1670976505125389195345303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1113984336750259463563535 1670976505125389195345303)
                ·
                  refine ⟨2506464757688083793017955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1670976505125389195345303 2506464757688083793017955)
                  ·
                    refine ⟨3759697136532125689526933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2506464757688083793017955 3759697136532125689526933)
                    ·
                      refine ⟨176235803274943391696575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3759697136532125689526933 176235803274943391696575)
                      ·
                        rfl

theorem cell23_343218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_343218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343218 prefixEnd_343218 := by exact prefixLift 343218
  have htrace : WordTrace (prefixWord ++ tailWord_343218) baseStart_343218 baseEnd_343218 := by
    simpa [prefixWord, tailWord_343218, baseEnd_343218] using wordTrace_append hprefix tailTrace_343218
  have hstable : (prefixWord ++ tailWord_343218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343218).length < 2 ^ (prefixWord ++ tailWord_343218).sum := by decide
  have hdescent : baseEnd_343218 < baseStart_343218 := by decide
  rcases family_descends (prefixWord ++ tailWord_343218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343225 : List Nat := [1, 2, 1, 4, 1, 3, 1, 4, 1, 2, 3]
def baseStart_343225 : Nat := 118140960795 + 343225 * 2 ^ 59
def prefixEnd_343225 : Nat := 4983230072969 + 3 ^ 40 * 343225 * 2
def baseEnd_343225 : Nat := 176239397639524864309043

theorem tailTrace_343225 : CollatzResearch.WordTrace tailWord_343225 prefixEnd_343225 176239397639524864309043 := by
  unfold tailWord_343225
  simp only [CollatzResearch.WordTrace]
  refine ⟨12518444181561918008279129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8345629454374612005519419 12518444181561918008279129)
  ·
    refine ⟨9388833136171438506209347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12518444181561918008279129 9388833136171438506209347)
    ·
      refine ⟨14083249704257157759314021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9388833136171438506209347 14083249704257157759314021)
      ·
        refine ⟨2640609319548217079871379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14083249704257157759314021 2640609319548217079871379)
        ·
          refine ⟨3960913979322325619807069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2640609319548217079871379 3960913979322325619807069)
          ·
            refine ⟨1485342742245872107427651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3960913979322325619807069 1485342742245872107427651)
            ·
              refine ⟨2228014113368808161141477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1485342742245872107427651 2228014113368808161141477)
              ·
                refine ⟨417752646256651530214027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2228014113368808161141477 417752646256651530214027)
                ·
                  refine ⟨626628969384977295321041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 417752646256651530214027 626628969384977295321041)
                  ·
                    refine ⟨469971727038732971490781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 626628969384977295321041 469971727038732971490781)
                    ·
                      refine ⟨176239397639524864309043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 469971727038732971490781 176239397639524864309043)
                      ·
                        rfl

theorem cell23_343225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_343225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343225 prefixEnd_343225 := by exact prefixLift 343225
  have htrace : WordTrace (prefixWord ++ tailWord_343225) baseStart_343225 baseEnd_343225 := by
    simpa [prefixWord, tailWord_343225, baseEnd_343225] using wordTrace_append hprefix tailTrace_343225
  have hstable : (prefixWord ++ tailWord_343225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343225).length < 2 ^ (prefixWord ++ tailWord_343225).sum := by decide
  have hdescent : baseEnd_343225 < baseStart_343225 := by decide
  rcases family_descends (prefixWord ++ tailWord_343225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343228 : List Nat := [2, 2, 2, 3, 2, 2, 1, 9]
def baseStart_343228 : Nat := 118140960795 + 343228 * 2 ^ 59
def prefixEnd_343228 : Nat := 4983230072969 + 3 ^ 40 * 343228 * 2
def baseEnd_343228 : Nat := 6527442151166235280427

theorem tailTrace_343228 : CollatzResearch.WordTrace tailWord_343228 prefixEnd_343228 6527442151166235280427 := by
  unfold tailWord_343228
  simp only [CollatzResearch.WordTrace]
  refine ⟨6259276800275524760319169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8345702400367366347092225 6259276800275524760319169)
  ·
    refine ⟨4694457600206643570239377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6259276800275524760319169 4694457600206643570239377)
    ·
      refine ⟨3520843200154982677679533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4694457600206643570239377 3520843200154982677679533)
      ·
        refine ⟨1320316200058118504129825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3520843200154982677679533 1320316200058118504129825)
        ·
          refine ⟨990237150043588878097369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1320316200058118504129825 990237150043588878097369)
          ·
            refine ⟨742677862532691658573027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 990237150043588878097369 742677862532691658573027)
            ·
              refine ⟨1114016793799037487859541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742677862532691658573027 1114016793799037487859541)
              ·
                refine ⟨6527442151166235280427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1114016793799037487859541 6527442151166235280427)
                ·
                  rfl

theorem cell23_343228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 9].length) (baseStart_343228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343228 prefixEnd_343228 := by exact prefixLift 343228
  have htrace : WordTrace (prefixWord ++ tailWord_343228) baseStart_343228 baseEnd_343228 := by
    simpa [prefixWord, tailWord_343228, baseEnd_343228] using wordTrace_append hprefix tailTrace_343228
  have hstable : (prefixWord ++ tailWord_343228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343228).length < 2 ^ (prefixWord ++ tailWord_343228).sum := by decide
  have hdescent : baseEnd_343228 < baseStart_343228 := by decide
  rcases family_descends (prefixWord ++ tailWord_343228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343255 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 4, 1, 3]
def baseStart_343255 : Nat := 118140960795 + 343255 * 2 ^ 59
def prefixEnd_343255 : Nat := 4983230072969 + 3 ^ 40 * 343255 * 2
def baseEnd_343255 : Nat := 176254802059159746933905

theorem tailTrace_343255 : CollatzResearch.WordTrace tailWord_343255 prefixEnd_343255 176254802059159746933905 := by
  unfold tailWord_343255
  simp only [CollatzResearch.WordTrace]
  refine ⟨12519538371453233131871219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8346358914302155421247479 12519538371453233131871219)
  ·
    refine ⟨18779307557179849697806829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12519538371453233131871219 18779307557179849697806829)
    ·
      refine ⟨7042240333942443636677561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18779307557179849697806829 7042240333942443636677561)
      ·
        refine ⟨5281680250456832727508171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7042240333942443636677561 5281680250456832727508171)
        ·
          refine ⟨7922520375685249091262257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5281680250456832727508171 7922520375685249091262257)
          ·
            refine ⟨5941890281763936818446693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7922520375685249091262257 5941890281763936818446693)
            ·
              refine ⟨1114104427830738153458755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5941890281763936818446693 1114104427830738153458755)
              ·
                refine ⟨1671156641746107230188133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114104427830738153458755 1671156641746107230188133)
                ·
                  refine ⟨313341870327395105660275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1671156641746107230188133 313341870327395105660275)
                  ·
                    refine ⟨470012805491092658490413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 313341870327395105660275 470012805491092658490413)
                    ·
                      refine ⟨176254802059159746933905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 470012805491092658490413 176254802059159746933905)
                      ·
                        rfl

theorem cell23_343255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 1, 3].length) (baseStart_343255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343255 prefixEnd_343255 := by exact prefixLift 343255
  have htrace : WordTrace (prefixWord ++ tailWord_343255) baseStart_343255 baseEnd_343255 := by
    simpa [prefixWord, tailWord_343255, baseEnd_343255] using wordTrace_append hprefix tailTrace_343255
  have hstable : (prefixWord ++ tailWord_343255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343255).length < 2 ^ (prefixWord ++ tailWord_343255).sum := by decide
  have hdescent : baseEnd_343255 < baseStart_343255 := by decide
  rcases family_descends (prefixWord ++ tailWord_343255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343256 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 3, 2, 2]
def baseStart_343256 : Nat := 118140960795 + 343256 * 2 ^ 59
def prefixEnd_343256 : Nat := 4983230072969 + 3 ^ 40 * 343256 * 2
def baseEnd_343256 : Nat := 176255315539814243021401

theorem tailTrace_343256 : CollatzResearch.WordTrace tailWord_343256 prefixEnd_343256 176255315539814243021401 := by
  unfold tailWord_343256
  simp only [CollatzResearch.WordTrace]
  refine ⟨6259787422224805151328811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8346383229633073535105081 6259787422224805151328811)
  ·
    refine ⟨9389681133337207726993217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6259787422224805151328811 9389681133337207726993217)
    ·
      refine ⟨7042260850002905795244913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9389681133337207726993217 7042260850002905795244913)
      ·
        refine ⟨5281695637502179346433685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7042260850002905795244913 5281695637502179346433685)
        ·
          refine ⟨247579483007914656864079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5281695637502179346433685 247579483007914656864079)
          ·
            refine ⟨371369224511871985296119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247579483007914656864079 371369224511871985296119)
            ·
              refine ⟨557053836767807977944179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371369224511871985296119 557053836767807977944179)
              ·
                refine ⟨835580755151711966916269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557053836767807977944179 835580755151711966916269)
                ·
                  refine ⟨313342783181891987593601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 835580755151711966916269 313342783181891987593601)
                  ·
                    refine ⟨235007087386418990695201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 313342783181891987593601 235007087386418990695201)
                    ·
                      refine ⟨176255315539814243021401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235007087386418990695201 176255315539814243021401)
                      ·
                        rfl

theorem cell23_343256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_343256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343256 prefixEnd_343256 := by exact prefixLift 343256
  have htrace : WordTrace (prefixWord ++ tailWord_343256) baseStart_343256 baseEnd_343256 := by
    simpa [prefixWord, tailWord_343256, baseEnd_343256] using wordTrace_append hprefix tailTrace_343256
  have hstable : (prefixWord ++ tailWord_343256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343256).length < 2 ^ (prefixWord ++ tailWord_343256).sum := by decide
  have hdescent : baseEnd_343256 < baseStart_343256 := by decide
  rcases family_descends (prefixWord ++ tailWord_343256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343272 : List Nat := [2, 1, 4, 1, 2, 1, 3, 3, 2, 1, 3]
def baseStart_343272 : Nat := 118140960795 + 343272 * 2 ^ 59
def prefixEnd_343272 : Nat := 4983230072969 + 3 ^ 40 * 343272 * 2
def baseEnd_343272 : Nat := 176263531230286180421327

theorem tailTrace_343272 : CollatzResearch.WordTrace tailWord_343272 prefixEnd_343272 176263531230286180421327 := by
  unfold tailWord_343272
  simp only [CollatzResearch.WordTrace]
  refine ⟨6260079206195822517620035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8346772274927763356826713 6260079206195822517620035)
  ·
    refine ⟨9390118809293733776430053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6260079206195822517620035 9390118809293733776430053)
    ·
      refine ⟨1760647276742575083080635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9390118809293733776430053 1760647276742575083080635)
      ·
        refine ⟨2640970915113862624620953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1760647276742575083080635 2640970915113862624620953)
        ·
          refine ⟨1980728186335396968465715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2640970915113862624620953 1980728186335396968465715)
          ·
            refine ⟨2971092279503095452698573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1980728186335396968465715 2971092279503095452698573)
            ·
              refine ⟨1114159604813660794761965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2971092279503095452698573 1114159604813660794761965)
              ·
                refine ⟨417809851805122798035737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1114159604813660794761965 417809851805122798035737)
                ·
                  refine ⟨313357388853842098526803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 417809851805122798035737 313357388853842098526803)
                  ·
                    refine ⟨470036083280763147790205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 313357388853842098526803 470036083280763147790205)
                    ·
                      refine ⟨176263531230286180421327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 470036083280763147790205 176263531230286180421327)
                      ·
                        rfl

theorem cell23_343272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_343272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343272 prefixEnd_343272 := by exact prefixLift 343272
  have htrace : WordTrace (prefixWord ++ tailWord_343272) baseStart_343272 baseEnd_343272 := by
    simpa [prefixWord, tailWord_343272, baseEnd_343272] using wordTrace_append hprefix tailTrace_343272
  have hstable : (prefixWord ++ tailWord_343272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343272).length < 2 ^ (prefixWord ++ tailWord_343272).sum := by decide
  have hdescent : baseEnd_343272 < baseStart_343272 := by decide
  rcases family_descends (prefixWord ++ tailWord_343272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343295 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 3, 4, 2]
def baseStart_343295 : Nat := 118140960795 + 343295 * 2 ^ 59
def prefixEnd_343295 : Nat := 4983230072969 + 3 ^ 40 * 343295 * 2
def baseEnd_343295 : Nat := 176275341285339590433721

theorem tailTrace_343295 : CollatzResearch.WordTrace tailWord_343295 prefixEnd_343295 176275341285339590433721 := by
  unfold tailWord_343295
  simp only [CollatzResearch.WordTrace]
  refine ⟨12520997291308319963327339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8347331527538879975551559 12520997291308319963327339)
  ·
    refine ⟨18781495936962479944991009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12520997291308319963327339 18781495936962479944991009)
    ·
      refine ⟨14086121952721859958743257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18781495936962479944991009 14086121952721859958743257)
      ·
        refine ⟨10564591464541394969057443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14086121952721859958743257 10564591464541394969057443)
        ·
          refine ⟨15846887196812092453586165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10564591464541394969057443 15846887196812092453586165)
          ·
            refine ⟨1485645674701133667523703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15846887196812092453586165 1485645674701133667523703)
            ·
              refine ⟨2228468512051700501285555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1485645674701133667523703 2228468512051700501285555)
              ·
                refine ⟨3342702768077550751928333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2228468512051700501285555 3342702768077550751928333)
                ·
                  refine ⟨1253513538029081531973125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3342702768077550751928333 1253513538029081531973125)
                  ·
                    refine ⟨235033788380452787244961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1253513538029081531973125 235033788380452787244961)
                    ·
                      refine ⟨176275341285339590433721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235033788380452787244961 176275341285339590433721)
                      ·
                        rfl

theorem cell23_343295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 4, 2].length) (baseStart_343295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343295 prefixEnd_343295 := by exact prefixLift 343295
  have htrace : WordTrace (prefixWord ++ tailWord_343295) baseStart_343295 baseEnd_343295 := by
    simpa [prefixWord, tailWord_343295, baseEnd_343295] using wordTrace_append hprefix tailTrace_343295
  have hstable : (prefixWord ++ tailWord_343295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343295).length < 2 ^ (prefixWord ++ tailWord_343295).sum := by decide
  have hdescent : baseEnd_343295 < baseStart_343295 := by decide
  rcases family_descends (prefixWord ++ tailWord_343295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343299 : List Nat := [1, 1, 1, 3, 2, 5, 3, 1, 1, 3, 2]
def baseStart_343299 : Nat := 118140960795 + 343299 * 2 ^ 59
def prefixEnd_343299 : Nat := 4983230072969 + 3 ^ 40 * 343299 * 2
def baseEnd_343299 : Nat := 176277395207957574783703

theorem tailTrace_343299 : CollatzResearch.WordTrace tailWord_343299 prefixEnd_343299 176277395207957574783703 := by
  unfold tailWord_343299
  simp only [CollatzResearch.WordTrace]
  refine ⟨12521143183293828646472951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8347428788862552430981967 12521143183293828646472951)
  ·
    refine ⟨18781714774940742969709427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12521143183293828646472951 18781714774940742969709427)
    ·
      refine ⟨28172572162411114454564141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18781714774940742969709427 28172572162411114454564141)
      ·
        refine ⟨10564714560904167920461553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28172572162411114454564141 10564714560904167920461553)
        ·
          refine ⟨7923535920678125940346165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10564714560904167920461553 7923535920678125940346165)
          ·
            refine ⟨742831492563574306907453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7923535920678125940346165 742831492563574306907453)
            ·
              refine ⟨278561809711340365090295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 742831492563574306907453 278561809711340365090295)
              ·
                refine ⟨417842714567010547635443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278561809711340365090295 417842714567010547635443)
                ·
                  refine ⟨626764071850515821453165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 417842714567010547635443 626764071850515821453165)
                  ·
                    refine ⟨235036526943943433044937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 626764071850515821453165 235036526943943433044937)
                    ·
                      refine ⟨176277395207957574783703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235036526943943433044937 176277395207957574783703)
                      ·
                        rfl

theorem cell23_343299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 1, 1, 3, 2].length) (baseStart_343299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343299 prefixEnd_343299 := by exact prefixLift 343299
  have htrace : WordTrace (prefixWord ++ tailWord_343299) baseStart_343299 baseEnd_343299 := by
    simpa [prefixWord, tailWord_343299, baseEnd_343299] using wordTrace_append hprefix tailTrace_343299
  have hstable : (prefixWord ++ tailWord_343299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343299).length < 2 ^ (prefixWord ++ tailWord_343299).sum := by decide
  have hdescent : baseEnd_343299 < baseStart_343299 := by decide
  rcases family_descends (prefixWord ++ tailWord_343299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343325 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_343325 : Nat := 118140960795 + 343325 * 2 ^ 59
def prefixEnd_343325 : Nat := 4983230072969 + 3 ^ 40 * 343325 * 2
def baseEnd_343325 : Nat := 176290745704974473058583

theorem tailTrace_343325 : CollatzResearch.WordTrace tailWord_343325 prefixEnd_343325 176290745704974473058583 := by
  unfold tailWord_343325
  simp only [CollatzResearch.WordTrace]
  refine ⟨12522091481199635086919429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8348060987466423391279619 12522091481199635086919429)
  ·
    refine ⟨2347892152724931578797393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12522091481199635086919429 2347892152724931578797393)
    ·
      refine ⟨1760919114543698684098045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2347892152724931578797393 1760919114543698684098045)
      ·
        refine ⟨660344667953887006536767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1760919114543698684098045 660344667953887006536767)
        ·
          refine ⟨990517001930830509805151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660344667953887006536767 990517001930830509805151)
          ·
            refine ⟨1485775502896245764707727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990517001930830509805151 1485775502896245764707727)
            ·
              refine ⟨2228663254344368647061591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1485775502896245764707727 2228663254344368647061591)
              ·
                refine ⟨3342994881516552970592387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2228663254344368647061591 3342994881516552970592387)
                ·
                  refine ⟨5014492322274829455888581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3342994881516552970592387 5014492322274829455888581)
                  ·
                    refine ⟨940217310426530522979109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5014492322274829455888581 940217310426530522979109)
                    ·
                      refine ⟨176290745704974473058583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 940217310426530522979109 176290745704974473058583)
                      ·
                        rfl

theorem cell23_343325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_343325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343325 prefixEnd_343325 := by exact prefixLift 343325
  have htrace : WordTrace (prefixWord ++ tailWord_343325) baseStart_343325 baseEnd_343325 := by
    simpa [prefixWord, tailWord_343325, baseEnd_343325] using wordTrace_append hprefix tailTrace_343325
  have hstable : (prefixWord ++ tailWord_343325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343325).length < 2 ^ (prefixWord ++ tailWord_343325).sum := by decide
  have hdescent : baseEnd_343325 < baseStart_343325 := by decide
  rcases family_descends (prefixWord ++ tailWord_343325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343350 : List Nat := [5, 1, 2, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_343350 : Nat := 118140960795 + 343350 * 2 ^ 59
def prefixEnd_343350 : Nat := 4983230072969 + 3 ^ 40 * 343350 * 2
def baseEnd_343350 : Nat := 176303582721336875245969

theorem tailTrace_343350 : CollatzResearch.WordTrace tailWord_343350 prefixEnd_343350 176303582721336875245969 := by
  unfold tailWord_343350
  simp only [CollatzResearch.WordTrace]
  refine ⟨782687706631816522286219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8348668870739376237719669 782687706631816522286219)
  ·
    refine ⟨1174031559947724783429329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 782687706631816522286219 1174031559947724783429329)
    ·
      refine ⟨880523669960793587571997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1174031559947724783429329 880523669960793587571997)
      ·
        refine ⟨330196376235297595339499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 880523669960793587571997 330196376235297595339499)
        ·
          refine ⟨495294564352946393009249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330196376235297595339499 495294564352946393009249)
          ·
            refine ⟨371470923264709794756937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 495294564352946393009249 371470923264709794756937)
            ·
              refine ⟨278603192448532346067703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371470923264709794756937 278603192448532346067703)
              ·
                refine ⟨417904788672798519101555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278603192448532346067703 417904788672798519101555)
                ·
                  refine ⟨626857183009197778652333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 417904788672798519101555 626857183009197778652333)
                  ·
                    refine ⟨235071443628449166994625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 626857183009197778652333 235071443628449166994625)
                    ·
                      refine ⟨176303582721336875245969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235071443628449166994625 176303582721336875245969)
                      ·
                        rfl

theorem cell23_343350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_343350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343350 prefixEnd_343350 := by exact prefixLift 343350
  have htrace : WordTrace (prefixWord ++ tailWord_343350) baseStart_343350 baseEnd_343350 := by
    simpa [prefixWord, tailWord_343350, baseEnd_343350] using wordTrace_append hprefix tailTrace_343350
  have hstable : (prefixWord ++ tailWord_343350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343350).length < 2 ^ (prefixWord ++ tailWord_343350).sum := by decide
  have hdescent : baseEnd_343350 < baseStart_343350 := by decide
  rcases family_descends (prefixWord ++ tailWord_343350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343408 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 10]
def baseStart_343408 : Nat := 118140960795 + 343408 * 2 ^ 59
def prefixEnd_343408 : Nat := 4983230072969 + 3 ^ 40 * 343408 * 2
def baseEnd_343408 : Nat := 19592596066588627591189

theorem tailTrace_343408 : CollatzResearch.WordTrace tailWord_343408 prefixEnd_343408 19592596066588627591189 := by
  unfold tailWord_343408
  simp only [CollatzResearch.WordTrace]
  refine ⟨6262559369949470131095439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8350079159932626841460585 6262559369949470131095439)
  ·
    refine ⟨9393839054924205196643159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6262559369949470131095439 9393839054924205196643159)
    ·
      refine ⟨14090758582386307794964739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9393839054924205196643159 14090758582386307794964739)
      ·
        refine ⟨21136137873579461692447109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14090758582386307794964739 21136137873579461692447109)
        ·
          refine ⟨3963025851296149067333833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21136137873579461692447109 3963025851296149067333833)
          ·
            refine ⟨2972269388472111800500375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3963025851296149067333833 2972269388472111800500375)
            ·
              refine ⟨4458404082708167700750563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2972269388472111800500375 4458404082708167700750563)
              ·
                refine ⟨6687606124062251551125845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4458404082708167700750563 6687606124062251551125845)
                ·
                  refine ⟨19592596066588627591189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 6687606124062251551125845 19592596066588627591189)
                  ·
                    rfl

theorem cell23_343408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 10].length) (baseStart_343408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343408 prefixEnd_343408 := by exact prefixLift 343408
  have htrace : WordTrace (prefixWord ++ tailWord_343408) baseStart_343408 baseEnd_343408 := by
    simpa [prefixWord, tailWord_343408, baseEnd_343408] using wordTrace_append hprefix tailTrace_343408
  have hstable : (prefixWord ++ tailWord_343408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343408).length < 2 ^ (prefixWord ++ tailWord_343408).sum := by decide
  have hdescent : baseEnd_343408 < baseStart_343408 := by decide
  rcases family_descends (prefixWord ++ tailWord_343408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343485 : List Nat := [1, 4, 1, 2, 2, 1, 1, 2, 3, 6]
def baseStart_343485 : Nat := 118140960795 + 343485 * 2 ^ 59
def prefixEnd_343485 : Nat := 4983230072969 + 3 ^ 40 * 343485 * 2
def baseEnd_343485 : Nat := 58790967536564615685949

theorem tailTrace_343485 : CollatzResearch.WordTrace tailWord_343485 prefixEnd_343485 58790967536564615685949 := by
  unfold tailWord_343485
  simp only [CollatzResearch.WordTrace]
  refine ⟨12527927160619982412743909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8351951440413321608495939 12527927160619982412743909)
  ·
    refine ⟨2348986342616246702389483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12527927160619982412743909 2348986342616246702389483)
    ·
      refine ⟨3523479513924370053584225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2348986342616246702389483 3523479513924370053584225)
      ·
        refine ⟨2642609635443277540188169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3523479513924370053584225 2642609635443277540188169)
        ·
          refine ⟨1981957226582458155141127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2642609635443277540188169 1981957226582458155141127)
          ·
            refine ⟨2972935839873687232711691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1981957226582458155141127 2972935839873687232711691)
            ·
              refine ⟨4459403759810530849067537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2972935839873687232711691 4459403759810530849067537)
              ·
                refine ⟨3344552819857898136800653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4459403759810530849067537 3344552819857898136800653)
                ·
                  refine ⟨1254207307446711801300245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3344552819857898136800653 1254207307446711801300245)
                  ·
                    refine ⟨58790967536564615685949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1254207307446711801300245 58790967536564615685949)
                    ·
                      rfl

theorem cell23_343485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_343485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343485 prefixEnd_343485 := by exact prefixLift 343485
  have htrace : WordTrace (prefixWord ++ tailWord_343485) baseStart_343485 baseEnd_343485 := by
    simpa [prefixWord, tailWord_343485, baseEnd_343485] using wordTrace_append hprefix tailTrace_343485
  have hstable : (prefixWord ++ tailWord_343485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343485).length < 2 ^ (prefixWord ++ tailWord_343485).sum := by decide
  have hdescent : baseEnd_343485 < baseStart_343485 := by decide
  rcases family_descends (prefixWord ++ tailWord_343485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343495 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 5]
def baseStart_343495 : Nat := 118140960795 + 343495 * 2 ^ 59
def prefixEnd_343495 : Nat := 4983230072969 + 3 ^ 40 * 343495 * 2
def baseEnd_343495 : Nat := 176378037416238807932801

theorem tailTrace_343495 : CollatzResearch.WordTrace tailWord_343495 prefixEnd_343495 176378037416238807932801 := by
  unfold tailWord_343495
  simp only [CollatzResearch.WordTrace]
  refine ⟨12528291890583754120607939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8352194593722502747071959 12528291890583754120607939)
  ·
    refine ⟨18792437835875631180911909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12528291890583754120607939 18792437835875631180911909)
    ·
      refine ⟨3523582094226680846420983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18792437835875631180911909 3523582094226680846420983)
      ·
        refine ⟨5285373141340021269631475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3523582094226680846420983 5285373141340021269631475)
        ·
          refine ⟨7928059712010031904447213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5285373141340021269631475 7928059712010031904447213)
          ·
            refine ⟨2973022392003761964167705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7928059712010031904447213 2973022392003761964167705)
            ·
              refine ⟨2229766794002821473125779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2973022392003761964167705 2229766794002821473125779)
              ·
                refine ⟨3344650191004232209688669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229766794002821473125779 3344650191004232209688669)
                ·
                  refine ⟨1254243821626587078633251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3344650191004232209688669 1254243821626587078633251)
                  ·
                    refine ⟨1881365732439880617949877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1254243821626587078633251 1881365732439880617949877)
                    ·
                      refine ⟨176378037416238807932801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1881365732439880617949877 176378037416238807932801)
                      ·
                        rfl

theorem cell23_343495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_343495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343495 prefixEnd_343495 := by exact prefixLift 343495
  have htrace : WordTrace (prefixWord ++ tailWord_343495) baseStart_343495 baseEnd_343495 := by
    simpa [prefixWord, tailWord_343495, baseEnd_343495] using wordTrace_append hprefix tailTrace_343495
  have hstable : (prefixWord ++ tailWord_343495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343495).length < 2 ^ (prefixWord ++ tailWord_343495).sum := by decide
  have hdescent : baseEnd_343495 < baseStart_343495 := by decide
  rcases family_descends (prefixWord ++ tailWord_343495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343512 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 3, 2, 3]
def baseStart_343512 : Nat := 118140960795 + 343512 * 2 ^ 59
def prefixEnd_343512 : Nat := 4983230072969 + 3 ^ 40 * 343512 * 2
def baseEnd_343512 : Nat := 176386766587365241420223

theorem tailTrace_343512 : CollatzResearch.WordTrace tailWord_343512 prefixEnd_343512 176386766587365241420223 := by
  unfold tailWord_343512
  simp only [CollatzResearch.WordTrace]
  refine ⟨6264455965761083011988395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8352607954348110682651193 6264455965761083011988395)
  ·
    refine ⟨9396683948641624517982593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6264455965761083011988395 9396683948641624517982593)
    ·
      refine ⟨7047512961481218388486945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9396683948641624517982593 7047512961481218388486945)
      ·
        refine ⟨5285634721110913791365209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7047512961481218388486945 5285634721110913791365209)
        ·
          refine ⟨3964226040833185343523907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5285634721110913791365209 3964226040833185343523907)
          ·
            refine ⟨5946339061249778015285861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3964226040833185343523907 5946339061249778015285861)
            ·
              refine ⟨1114938573984333377866099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5946339061249778015285861 1114938573984333377866099)
              ·
                refine ⟨1672407860976500066799149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114938573984333377866099 1672407860976500066799149)
                ·
                  refine ⟨627152947866187525049681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1672407860976500066799149 627152947866187525049681)
                  ·
                    refine ⟨470364710899640643787261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 627152947866187525049681 470364710899640643787261)
                    ·
                      refine ⟨176386766587365241420223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 470364710899640643787261 176386766587365241420223)
                      ·
                        rfl

theorem cell23_343512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_343512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343512 prefixEnd_343512 := by exact prefixLift 343512
  have htrace : WordTrace (prefixWord ++ tailWord_343512) baseStart_343512 baseEnd_343512 := by
    simpa [prefixWord, tailWord_343512, baseEnd_343512] using wordTrace_append hprefix tailTrace_343512
  have hstable : (prefixWord ++ tailWord_343512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343512).length < 2 ^ (prefixWord ++ tailWord_343512).sum := by decide
  have hdescent : baseEnd_343512 < baseStart_343512 := by decide
  rcases family_descends (prefixWord ++ tailWord_343512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343556 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_343556 : Nat := 118140960795 + 343556 * 2 ^ 59
def prefixEnd_343556 : Nat := 4983230072969 + 3 ^ 40 * 343556 * 2
def baseEnd_343556 : Nat := 176409359736163069270021

theorem tailTrace_343556 : CollatzResearch.WordTrace tailWord_343556 prefixEnd_343556 176409359736163069270021 := by
  unfold tailWord_343556
  simp only [CollatzResearch.WordTrace]
  refine ⟨6265258371681380769289261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8353677828908507692385681 6265258371681380769289261)
  ·
    refine ⟨2349471889380517788483473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6265258371681380769289261 2349471889380517788483473)
    ·
      refine ⟨1762103917035388341362605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2349471889380517788483473 1762103917035388341362605)
      ·
        refine ⟨660788968888270628010977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1762103917035388341362605 660788968888270628010977)
        ·
          refine ⟨495591726666202971008233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 660788968888270628010977 495591726666202971008233)
          ·
            refine ⟨371693794999652228256175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 495591726666202971008233 371693794999652228256175)
            ·
              refine ⟨557540692499478342384263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371693794999652228256175 557540692499478342384263)
              ·
                refine ⟨836311038749217513576395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557540692499478342384263 836311038749217513576395)
                ·
                  refine ⟨1254466558123826270364593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 836311038749217513576395 1254466558123826270364593)
                  ·
                    refine ⟨940849918592869702773445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1254466558123826270364593 940849918592869702773445)
                    ·
                      refine ⟨176409359736163069270021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 940849918592869702773445 176409359736163069270021)
                      ·
                        rfl

theorem cell23_343556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_343556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343556 prefixEnd_343556 := by exact prefixLift 343556
  have htrace : WordTrace (prefixWord ++ tailWord_343556) baseStart_343556 baseEnd_343556 := by
    simpa [prefixWord, tailWord_343556, baseEnd_343556] using wordTrace_append hprefix tailTrace_343556
  have hstable : (prefixWord ++ tailWord_343556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343556).length < 2 ^ (prefixWord ++ tailWord_343556).sum := by decide
  have hdescent : baseEnd_343556 < baseStart_343556 := by decide
  rcases family_descends (prefixWord ++ tailWord_343556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343559 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 3]
def baseStart_343559 : Nat := 118140960795 + 343559 * 2 ^ 59
def prefixEnd_343559 : Nat := 4983230072969 + 3 ^ 40 * 343559 * 2
def baseEnd_343559 : Nat := 176410900178126557532507

theorem tailTrace_343559 : CollatzResearch.WordTrace tailWord_343559 prefixEnd_343559 176410900178126557532507 := by
  unfold tailWord_343559
  simp only [CollatzResearch.WordTrace]
  refine ⟨12530626162351893050937731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8353750774901262033958487 12530626162351893050937731)
  ·
    refine ⟨18795939243527839576406597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12530626162351893050937731 18795939243527839576406597)
    ·
      refine ⟨3524238608161469920576237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18795939243527839576406597 3524238608161469920576237)
      ·
        refine ⟨1321589478060551220216089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3524238608161469920576237 1321589478060551220216089)
        ·
          refine ⟨991192108545413415162067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1321589478060551220216089 991192108545413415162067)
          ·
            refine ⟨1486788162818120122743101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991192108545413415162067 1486788162818120122743101)
            ·
              refine ⟨557545561056795046028663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1486788162818120122743101 557545561056795046028663)
              ·
                refine ⟨836318341585192569042995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557545561056795046028663 836318341585192569042995)
                ·
                  refine ⟨1254477512377788853564493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 836318341585192569042995 1254477512377788853564493)
                  ·
                    refine ⟨470429067141670820086685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1254477512377788853564493 470429067141670820086685)
                    ·
                      refine ⟨176410900178126557532507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 470429067141670820086685 176410900178126557532507)
                      ·
                        rfl

theorem cell23_343559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_343559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343559 prefixEnd_343559 := by exact prefixLift 343559
  have htrace : WordTrace (prefixWord ++ tailWord_343559) baseStart_343559 baseEnd_343559 := by
    simpa [prefixWord, tailWord_343559, baseEnd_343559] using wordTrace_append hprefix tailTrace_343559
  have hstable : (prefixWord ++ tailWord_343559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343559).length < 2 ^ (prefixWord ++ tailWord_343559).sum := by decide
  have hdescent : baseEnd_343559 < baseStart_343559 := by decide
  rcases family_descends (prefixWord ++ tailWord_343559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343566 : List Nat := [4, 1, 1, 2, 5, 1, 2, 7]
def baseStart_343566 : Nat := 118140960795 + 343566 * 2 ^ 59
def prefixEnd_343566 : Nat := 4983230072969 + 3 ^ 40 * 343566 * 2
def baseEnd_343566 : Nat := 6533870168248445560925

theorem tailTrace_343566 : CollatzResearch.WordTrace tailWord_343566 prefixEnd_343566 6533870168248445560925 := by
  unfold tailWord_343566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1566360184165816655805319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8353920982217688830961701 1566360184165816655805319)
  ·
    refine ⟨2349540276248724983707979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1566360184165816655805319 2349540276248724983707979)
    ·
      refine ⟨3524310414373087475561969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2349540276248724983707979 3524310414373087475561969)
      ·
        refine ⟨2643232810779815606671477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3524310414373087475561969 2643232810779815606671477)
        ·
          refine ⟨247803076010607713125451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2643232810779815606671477 247803076010607713125451)
          ·
            refine ⟨371704614015911569688177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247803076010607713125451 371704614015911569688177)
            ·
              refine ⟨278778460511933677266133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371704614015911569688177 278778460511933677266133)
              ·
                refine ⟨6533870168248445560925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 278778460511933677266133 6533870168248445560925)
                ·
                  rfl

theorem cell23_343566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 7].length) (baseStart_343566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343566 prefixEnd_343566 := by exact prefixLift 343566
  have htrace : WordTrace (prefixWord ++ tailWord_343566) baseStart_343566 baseEnd_343566 := by
    simpa [prefixWord, tailWord_343566, baseEnd_343566] using wordTrace_append hprefix tailTrace_343566
  have hstable : (prefixWord ++ tailWord_343566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343566).length < 2 ^ (prefixWord ++ tailWord_343566).sum := by decide
  have hdescent : baseEnd_343566 < baseStart_343566 := by decide
  rcases family_descends (prefixWord ++ tailWord_343566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343586 : List Nat := [3, 3, 1, 1, 1, 1, 4, 3, 1, 3, 2]
def baseStart_343586 : Nat := 118140960795 + 343586 * 2 ^ 59
def prefixEnd_343586 : Nat := 4983230072969 + 3 ^ 40 * 343586 * 2
def baseEnd_343586 : Nat := 176424764155797951894883

theorem tailTrace_343586 : CollatzResearch.WordTrace tailWord_343586 prefixEnd_343586 176424764155797951894883 := by
  unfold tailWord_343586
  simp only [CollatzResearch.WordTrace]
  refine ⟨3132902733313519165542653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8354407288836051108113741 3132902733313519165542653)
  ·
    refine ⟨1174838524992569687078495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3132902733313519165542653 1174838524992569687078495)
    ·
      refine ⟨1762257787488854530617743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1174838524992569687078495 1762257787488854530617743)
      ·
        refine ⟨2643386681233281795926615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1762257787488854530617743 2643386681233281795926615)
        ·
          refine ⟨3965080021849922693889923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2643386681233281795926615 3965080021849922693889923)
          ·
            refine ⟨5947620032774884040834885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3965080021849922693889923 5947620032774884040834885)
            ·
              refine ⟨1115178756145290757656541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5947620032774884040834885 1115178756145290757656541)
              ·
                refine ⟨418192033554484034121203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1115178756145290757656541 418192033554484034121203)
                ·
                  refine ⟨627288050331726051181805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 418192033554484034121203 627288050331726051181805)
                  ·
                    refine ⟨235233018874397269193177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 627288050331726051181805 235233018874397269193177)
                    ·
                      refine ⟨176424764155797951894883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235233018874397269193177 176424764155797951894883)
                      ·
                        rfl

theorem cell23_343586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_343586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343586 prefixEnd_343586 := by exact prefixLift 343586
  have htrace : WordTrace (prefixWord ++ tailWord_343586) baseStart_343586 baseEnd_343586 := by
    simpa [prefixWord, tailWord_343586, baseEnd_343586] using wordTrace_append hprefix tailTrace_343586
  have hstable : (prefixWord ++ tailWord_343586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343586).length < 2 ^ (prefixWord ++ tailWord_343586).sum := by decide
  have hdescent : baseEnd_343586 < baseStart_343586 := by decide
  rcases family_descends (prefixWord ++ tailWord_343586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343602 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3]
def baseStart_343602 : Nat := 118140960795 + 343602 * 2 ^ 59
def prefixEnd_343602 : Nat := 4983230072969 + 3 ^ 40 * 343602 * 2
def baseEnd_343602 : Nat := 176432979846269889294809

theorem tailTrace_343602 : CollatzResearch.WordTrace tailWord_343602 prefixEnd_343602 176432979846269889294809 := by
  unfold tailWord_343602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3133048625299027848688265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8354796334130740929835373 3133048625299027848688265)
  ·
    refine ⟨2349786468974270886516199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3133048625299027848688265 2349786468974270886516199)
    ·
      refine ⟨3524679703461406329774299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2349786468974270886516199 3524679703461406329774299)
      ·
        refine ⟨5287019555192109494661449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3524679703461406329774299 5287019555192109494661449)
        ·
          refine ⟨3965264666394082120996087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5287019555192109494661449 3965264666394082120996087)
          ·
            refine ⟨5947896999591123181494131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3965264666394082120996087 5947896999591123181494131)
            ·
              refine ⟨8921845499386684772241197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5947896999591123181494131 8921845499386684772241197)
              ·
                refine ⟨3345692062270006789590449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8921845499386684772241197 3345692062270006789590449)
                ·
                  refine ⟨2509269046702505092192837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3345692062270006789590449 2509269046702505092192837)
                  ·
                    refine ⟨470487946256719704786157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2509269046702505092192837 470487946256719704786157)
                    ·
                      refine ⟨176432979846269889294809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 470487946256719704786157 176432979846269889294809)
                      ·
                        rfl

theorem cell23_343602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_343602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343602 prefixEnd_343602 := by exact prefixLift 343602
  have htrace : WordTrace (prefixWord ++ tailWord_343602) baseStart_343602 baseEnd_343602 := by
    simpa [prefixWord, tailWord_343602, baseEnd_343602] using wordTrace_append hprefix tailTrace_343602
  have hstable : (prefixWord ++ tailWord_343602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343602).length < 2 ^ (prefixWord ++ tailWord_343602).sum := by decide
  have hdescent : baseEnd_343602 < baseStart_343602 := by decide
  rcases family_descends (prefixWord ++ tailWord_343602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343625 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 8]
def baseStart_343625 : Nat := 118140960795 + 343625 * 2 ^ 59
def prefixEnd_343625 : Nat := 4983230072969 + 3 ^ 40 * 343625 * 2
def baseEnd_343625 : Nat := 176444789901323299307203

theorem tailTrace_343625 : CollatzResearch.WordTrace tailWord_343625 prefixEnd_343625 176444789901323299307203 := by
  unfold tailWord_343625
  simp only [CollatzResearch.WordTrace]
  refine ⟨12533033380112786322840329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8355355586741857548560219 12533033380112786322840329)
  ·
    refine ⟨9399775035084589742130247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12533033380112786322840329 9399775035084589742130247)
    ·
      refine ⟨14099662552626884613195371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9399775035084589742130247 14099662552626884613195371)
      ·
        refine ⟨21149493828940326919793057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14099662552626884613195371 21149493828940326919793057)
        ·
          refine ⟨15862120371705245189844793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21149493828940326919793057 15862120371705245189844793)
          ·
            refine ⟨11896590278778933892383595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15862120371705245189844793 11896590278778933892383595)
            ·
              refine ⟨17844885418168400838575393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11896590278778933892383595 17844885418168400838575393)
              ·
                refine ⟨13383664063626300628931545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17844885418168400838575393 13383664063626300628931545)
                ·
                  refine ⟨10037748047719725471698659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13383664063626300628931545 10037748047719725471698659)
                  ·
                    refine ⟨15056622071579588207547989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10037748047719725471698659 15056622071579588207547989)
                    ·
                      refine ⟨176444789901323299307203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 15056622071579588207547989 176444789901323299307203)
                      ·
                        rfl

theorem cell23_343625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_343625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343625 prefixEnd_343625 := by exact prefixLift 343625
  have htrace : WordTrace (prefixWord ++ tailWord_343625) baseStart_343625 baseEnd_343625 := by
    simpa [prefixWord, tailWord_343625, baseEnd_343625] using wordTrace_append hprefix tailTrace_343625
  have hstable : (prefixWord ++ tailWord_343625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343625).length < 2 ^ (prefixWord ++ tailWord_343625).sum := by decide
  have hdescent : baseEnd_343625 < baseStart_343625 := by decide
  rcases family_descends (prefixWord ++ tailWord_343625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343656 : List Nat := [2, 1, 4, 3, 1, 2, 1, 4, 5]
def baseStart_343656 : Nat := 118140960795 + 343656 * 2 ^ 59
def prefixEnd_343656 : Nat := 4983230072969 + 3 ^ 40 * 343656 * 2
def baseEnd_343656 : Nat := 19606745311290297557729

theorem tailTrace_343656 : CollatzResearch.WordTrace tailWord_343656 prefixEnd_343656 19606745311290297557729 := by
  unfold tailWord_343656
  simp only [CollatzResearch.WordTrace]
  refine ⟨6267082021500239308609411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8356109362000319078145881 6267082021500239308609411)
  ·
    refine ⟨9400623032250358962914117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6267082021500239308609411 9400623032250358962914117)
    ·
      refine ⟨1762616818546942305546397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9400623032250358962914117 1762616818546942305546397)
      ·
        refine ⟨660981306955103364579899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1762616818546942305546397 660981306955103364579899)
        ·
          refine ⟨991471960432655046869849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660981306955103364579899 991471960432655046869849)
          ·
            refine ⟨743603970324491285152387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 991471960432655046869849 743603970324491285152387)
            ·
              refine ⟨1115405955486736927728581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743603970324491285152387 1115405955486736927728581)
              ·
                refine ⟨209138616653763173949109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1115405955486736927728581 209138616653763173949109)
                ·
                  refine ⟨19606745311290297557729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 209138616653763173949109 19606745311290297557729)
                  ·
                    rfl

theorem cell23_343656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 1, 4, 5].length) (baseStart_343656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343656 prefixEnd_343656 := by exact prefixLift 343656
  have htrace : WordTrace (prefixWord ++ tailWord_343656) baseStart_343656 baseEnd_343656 := by
    simpa [prefixWord, tailWord_343656, baseEnd_343656] using wordTrace_append hprefix tailTrace_343656
  have hstable : (prefixWord ++ tailWord_343656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343656).length < 2 ^ (prefixWord ++ tailWord_343656).sum := by decide
  have hdescent : baseEnd_343656 < baseStart_343656 := by decide
  rcases family_descends (prefixWord ++ tailWord_343656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343689 : List Nat := [1, 2, 1, 1, 4, 1, 5, 1, 2, 1, 4]
def baseStart_343689 : Nat := 118140960795 + 343689 * 2 ^ 59
def prefixEnd_343689 : Nat := 4983230072969 + 3 ^ 40 * 343689 * 2
def baseEnd_343689 : Nat := 176477652663211048906909

theorem tailTrace_343689 : CollatzResearch.WordTrace tailWord_343689 prefixEnd_343689 176477652663211048906909 := by
  unfold tailWord_343689
  simp only [CollatzResearch.WordTrace]
  refine ⟨12535367651880925253170121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8356911767920616835446747 12535367651880925253170121)
  ·
    refine ⟨9401525738910693939877591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12535367651880925253170121 9401525738910693939877591)
    ·
      refine ⟨14102288608366040909816387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9401525738910693939877591 14102288608366040909816387)
      ·
        refine ⟨21153432912549061364724581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14102288608366040909816387 21153432912549061364724581)
        ·
          refine ⟨3966268671102949005885859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21153432912549061364724581 3966268671102949005885859)
          ·
            refine ⟨5949403006654423508828789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3966268671102949005885859 5949403006654423508828789)
            ·
              refine ⟨557756531873852203952699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5949403006654423508828789 557756531873852203952699)
              ·
                refine ⟨836634797810778305929049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557756531873852203952699 836634797810778305929049)
                ·
                  refine ⟨627476098358083729446787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 836634797810778305929049 627476098358083729446787)
                  ·
                    refine ⟨941214147537125594170181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 627476098358083729446787 941214147537125594170181)
                    ·
                      refine ⟨176477652663211048906909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 941214147537125594170181 176477652663211048906909)
                      ·
                        rfl

theorem cell23_343689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 1, 4].length) (baseStart_343689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343689 prefixEnd_343689 := by exact prefixLift 343689
  have htrace : WordTrace (prefixWord ++ tailWord_343689) baseStart_343689 baseEnd_343689 := by
    simpa [prefixWord, tailWord_343689, baseEnd_343689] using wordTrace_append hprefix tailTrace_343689
  have hstable : (prefixWord ++ tailWord_343689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343689).length < 2 ^ (prefixWord ++ tailWord_343689).sum := by decide
  have hdescent : baseEnd_343689 < baseStart_343689 := by decide
  rcases family_descends (prefixWord ++ tailWord_343689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343709 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_343709 : Nat := 118140960795 + 343709 * 2 ^ 59
def prefixEnd_343709 : Nat := 4983230072969 + 3 ^ 40 * 343709 * 2
def baseEnd_343709 : Nat := 176487922276300970656817

theorem tailTrace_343709 : CollatzResearch.WordTrace tailWord_343709 prefixEnd_343709 176487922276300970656817 := by
  unfold tailWord_343709
  simp only [CollatzResearch.WordTrace]
  refine ⟨12536097111808468668898181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8357398074538979112598787 12536097111808468668898181)
  ·
    refine ⟨2350518208464087875418409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12536097111808468668898181 2350518208464087875418409)
    ·
      refine ⟨1762888656348065906563807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2350518208464087875418409 1762888656348065906563807)
      ·
        refine ⟨2644332984522098859845711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1762888656348065906563807 2644332984522098859845711)
        ·
          refine ⟨3966499476783148289768567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2644332984522098859845711 3966499476783148289768567)
          ·
            refine ⟨5949749215174722434652851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3966499476783148289768567 5949749215174722434652851)
            ·
              refine ⟨8924623822762083651979277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5949749215174722434652851 8924623822762083651979277)
              ·
                refine ⟨3346733933535781369492229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8924623822762083651979277 3346733933535781369492229)
                ·
                  refine ⟨627512612537959006779793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3346733933535781369492229 627512612537959006779793)
                  ·
                    refine ⟨470634459403469255084845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 627512612537959006779793 470634459403469255084845)
                    ·
                      refine ⟨176487922276300970656817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 470634459403469255084845 176487922276300970656817)
                      ·
                        rfl

theorem cell23_343709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_343709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343709 prefixEnd_343709 := by exact prefixLift 343709
  have htrace : WordTrace (prefixWord ++ tailWord_343709) baseStart_343709 baseEnd_343709 := by
    simpa [prefixWord, tailWord_343709, baseEnd_343709] using wordTrace_append hprefix tailTrace_343709
  have hstable : (prefixWord ++ tailWord_343709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343709).length < 2 ^ (prefixWord ++ tailWord_343709).sum := by decide
  have hdescent : baseEnd_343709 < baseStart_343709 := by decide
  rcases family_descends (prefixWord ++ tailWord_343709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343716 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 3, 4]
def baseStart_343716 : Nat := 118140960795 + 343716 * 2 ^ 59
def prefixEnd_343716 : Nat := 4983230072969 + 3 ^ 40 * 343716 * 2
def baseEnd_343716 : Nat := 58830505546960814423095

theorem tailTrace_343716 : CollatzResearch.WordTrace tailWord_343716 prefixEnd_343716 58830505546960814423095 := by
  unfold tailWord_343716
  simp only [CollatzResearch.WordTrace]
  refine ⟨6268176211391554432201501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8357568281855405909602001 6268176211391554432201501)
  ·
    refine ⟨2350566079271832912075563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6268176211391554432201501 2350566079271832912075563)
    ·
      refine ⟨3525849118907749368113345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2350566079271832912075563 3525849118907749368113345)
      ·
        refine ⟨2644386839180812026085009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3525849118907749368113345 2644386839180812026085009)
        ·
          refine ⟨1983290129385609019563757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2644386839180812026085009 1983290129385609019563757)
          ·
            refine ⟨743733798519603382336409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1983290129385609019563757 743733798519603382336409)
            ·
              refine ⟨557800348889702536752307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743733798519603382336409 557800348889702536752307)
              ·
                refine ⟨836700523334553805128461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557800348889702536752307 836700523334553805128461)
                ·
                  refine ⟨313762696250457676923173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 836700523334553805128461 313762696250457676923173)
                  ·
                    refine ⟨58830505546960814423095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 313762696250457676923173 58830505546960814423095)
                    ·
                      rfl

theorem cell23_343716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_343716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343716 prefixEnd_343716 := by exact prefixLift 343716
  have htrace : WordTrace (prefixWord ++ tailWord_343716) baseStart_343716 baseEnd_343716 := by
    simpa [prefixWord, tailWord_343716, baseEnd_343716] using wordTrace_append hprefix tailTrace_343716
  have hstable : (prefixWord ++ tailWord_343716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343716).length < 2 ^ (prefixWord ++ tailWord_343716).sum := by decide
  have hdescent : baseEnd_343716 < baseStart_343716 := by decide
  rcases family_descends (prefixWord ++ tailWord_343716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343809 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 3, 2, 4]
def baseStart_343809 : Nat := 118140960795 + 343809 * 2 ^ 59
def prefixEnd_343809 : Nat := 4983230072969 + 3 ^ 40 * 343809 * 2
def baseEnd_343809 : Nat := 176539270341750579406357

theorem tailTrace_343809 : CollatzResearch.WordTrace tailWord_343809 prefixEnd_343809 176539270341750579406357 := by
  unfold tailWord_343809
  simp only [CollatzResearch.WordTrace]
  refine ⟨12539744411446185747538481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8359829607630790498358987 12539744411446185747538481)
  ·
    refine ⟨9404808308584639310653861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12539744411446185747538481 9404808308584639310653861)
    ·
      refine ⟨1763401557859619870747599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9404808308584639310653861 1763401557859619870747599)
      ·
        refine ⟨2645102336789429806121399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1763401557859619870747599 2645102336789429806121399)
        ·
          refine ⟨3967653505184144709182099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2645102336789429806121399 3967653505184144709182099)
          ·
            refine ⟨5951480257776217063773149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3967653505184144709182099 5951480257776217063773149)
            ·
              refine ⟨2231805096666081398914931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5951480257776217063773149 2231805096666081398914931)
              ·
                refine ⟨3347707644999122098372397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2231805096666081398914931 3347707644999122098372397)
                ·
                  refine ⟨1255390366874670786889649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3347707644999122098372397 1255390366874670786889649)
                  ·
                    refine ⟨941542775156003090167237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1255390366874670786889649 941542775156003090167237)
                    ·
                      refine ⟨176539270341750579406357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 941542775156003090167237 176539270341750579406357)
                      ·
                        rfl

theorem cell23_343809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_343809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343809 prefixEnd_343809 := by exact prefixLift 343809
  have htrace : WordTrace (prefixWord ++ tailWord_343809) baseStart_343809 baseEnd_343809 := by
    simpa [prefixWord, tailWord_343809, baseEnd_343809] using wordTrace_append hprefix tailTrace_343809
  have hstable : (prefixWord ++ tailWord_343809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343809).length < 2 ^ (prefixWord ++ tailWord_343809).sum := by decide
  have hdescent : baseEnd_343809 < baseStart_343809 := by decide
  rcases family_descends (prefixWord ++ tailWord_343809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343814 : List Nat := [6, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_343814 : Nat := 118140960795 + 343814 * 2 ^ 59
def prefixEnd_343814 : Nat := 4983230072969 + 3 ^ 40 * 343814 * 2
def baseEnd_343814 : Nat := 19615759749447006649315

theorem tailTrace_343814 : CollatzResearch.WordTrace tailWord_343814 prefixEnd_343814 19615759749447006649315 := by
  unfold tailWord_343814
  simp only [CollatzResearch.WordTrace]
  refine ⟨391872711763377237545953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8359951184285381067646997 391872711763377237545953)
  ·
    refine ⟨293904533822532928159465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 391872711763377237545953 293904533822532928159465)
    ·
      refine ⟨220428400366899696119599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293904533822532928159465 220428400366899696119599)
      ·
        refine ⟨330642600550349544179399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220428400366899696119599 330642600550349544179399)
        ·
          refine ⟨495963900825524316269099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330642600550349544179399 495963900825524316269099)
          ·
            refine ⟨743945851238286474403649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495963900825524316269099 743945851238286474403649)
            ·
              refine ⟨557959388428714855802737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743945851238286474403649 557959388428714855802737)
              ·
                refine ⟨418469541321536141852053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557959388428714855802737 418469541321536141852053)
                ·
                  refine ⟨19615759749447006649315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 418469541321536141852053 19615759749447006649315)
                  ·
                    rfl

theorem cell23_343814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_343814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343814 prefixEnd_343814 := by exact prefixLift 343814
  have htrace : WordTrace (prefixWord ++ tailWord_343814) baseStart_343814 baseEnd_343814 := by
    simpa [prefixWord, tailWord_343814, baseEnd_343814] using wordTrace_append hprefix tailTrace_343814
  have hstable : (prefixWord ++ tailWord_343814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343814).length < 2 ^ (prefixWord ++ tailWord_343814).sum := by decide
  have hdescent : baseEnd_343814 < baseStart_343814 := by decide
  rcases family_descends (prefixWord ++ tailWord_343814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343879 : List Nat := [1, 1, 4, 1, 2, 1, 3, 2, 2, 6]
def baseStart_343879 : Nat := 118140960795 + 343879 * 2 ^ 59
def prefixEnd_343879 : Nat := 4983230072969 + 3 ^ 40 * 343879 * 2
def baseEnd_343879 : Nat := 58858404662521768510345

theorem tailTrace_343879 : CollatzResearch.WordTrace tailWord_343879 prefixEnd_343879 58858404662521768510345 := by
  unfold tailWord_343879
  simp only [CollatzResearch.WordTrace]
  refine ⟨12542297521192587702586691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8361531680795058468391127 12542297521192587702586691)
  ·
    refine ⟨18813446281788881553880037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12542297521192587702586691 18813446281788881553880037)
    ·
      refine ⟨3527521177835415291352507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18813446281788881553880037 3527521177835415291352507)
      ·
        refine ⟨5291281766753122937028761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3527521177835415291352507 5291281766753122937028761)
        ·
          refine ⟨3968461325064842202771571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5291281766753122937028761 3968461325064842202771571)
          ·
            refine ⟨5952691987597263304157357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3968461325064842202771571 5952691987597263304157357)
            ·
              refine ⟨2232259495348973739059009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5952691987597263304157357 2232259495348973739059009)
              ·
                refine ⟨1674194621511730304294257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2232259495348973739059009 1674194621511730304294257)
                ·
                  refine ⟨1255645966133797728220693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1674194621511730304294257 1255645966133797728220693)
                  ·
                    refine ⟨58858404662521768510345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1255645966133797728220693 58858404662521768510345)
                    ·
                      rfl

theorem cell23_343879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_343879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343879 prefixEnd_343879 := by exact prefixLift 343879
  have htrace : WordTrace (prefixWord ++ tailWord_343879) baseStart_343879 baseEnd_343879 := by
    simpa [prefixWord, tailWord_343879, baseEnd_343879] using wordTrace_append hprefix tailTrace_343879
  have hstable : (prefixWord ++ tailWord_343879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343879).length < 2 ^ (prefixWord ++ tailWord_343879).sum := by decide
  have hdescent : baseEnd_343879 < baseStart_343879 := by decide
  rcases family_descends (prefixWord ++ tailWord_343879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343880 : List Nat := [2, 1, 3, 1, 1, 6, 1, 2, 2, 1, 3]
def baseStart_343880 : Nat := 118140960795 + 343880 * 2 ^ 59
def prefixEnd_343880 : Nat := 4983230072969 + 3 ^ 40 * 343880 * 2
def baseEnd_343880 : Nat := 176575727468219801618531

theorem tailTrace_343880 : CollatzResearch.WordTrace tailWord_343880 prefixEnd_343880 176575727468219801618531 := by
  unfold tailWord_343880
  simp only [CollatzResearch.WordTrace]
  refine ⟨6271166997094482436686547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8361555996125976582248729 6271166997094482436686547)
  ·
    refine ⟨9406750495641723655029821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6271166997094482436686547 9406750495641723655029821)
    ·
      refine ⟨3527531435865646370636183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9406750495641723655029821 3527531435865646370636183)
      ·
        refine ⟨5291297153798469555954275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3527531435865646370636183 5291297153798469555954275)
        ·
          refine ⟨7936945730697704333931413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5291297153798469555954275 7936945730697704333931413)
          ·
            refine ⟨372044331126454890653035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7936945730697704333931413 372044331126454890653035)
            ·
              refine ⟨558066496689682335979553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372044331126454890653035 558066496689682335979553)
              ·
                refine ⟨418549872517261751984665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558066496689682335979553 418549872517261751984665)
                ·
                  refine ⟨313912404387946313988499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418549872517261751984665 313912404387946313988499)
                  ·
                    refine ⟨470868606581919470982749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 313912404387946313988499 470868606581919470982749)
                    ·
                      refine ⟨176575727468219801618531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 470868606581919470982749 176575727468219801618531)
                      ·
                        rfl

theorem cell23_343880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_343880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343880 prefixEnd_343880 := by exact prefixLift 343880
  have htrace : WordTrace (prefixWord ++ tailWord_343880) baseStart_343880 baseEnd_343880 := by
    simpa [prefixWord, tailWord_343880, baseEnd_343880] using wordTrace_append hprefix tailTrace_343880
  have hstable : (prefixWord ++ tailWord_343880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343880).length < 2 ^ (prefixWord ++ tailWord_343880).sum := by decide
  have hdescent : baseEnd_343880 < baseStart_343880 := by decide
  rcases family_descends (prefixWord ++ tailWord_343880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343886 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2]
def baseStart_343886 : Nat := 118140960795 + 343886 * 2 ^ 59
def prefixEnd_343886 : Nat := 4983230072969 + 3 ^ 40 * 343886 * 2
def baseEnd_343886 : Nat := 176578808352146778143503

theorem tailTrace_343886 : CollatzResearch.WordTrace tailWord_343886 prefixEnd_343886 176578808352146778143503 := by
  unfold tailWord_343886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1567819104020903487261439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8361701888111485265394341 1567819104020903487261439)
  ·
    refine ⟨2351728656031355230892159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1567819104020903487261439 2351728656031355230892159)
    ·
      refine ⟨3527592984047032846338239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2351728656031355230892159 3527592984047032846338239)
      ·
        refine ⟨5291389476070549269507359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3527592984047032846338239 5291389476070549269507359)
        ·
          refine ⟨7937084214105823904261039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5291389476070549269507359 7937084214105823904261039)
          ·
            refine ⟨11905626321158735856391559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7937084214105823904261039 11905626321158735856391559)
            ·
              refine ⟨17858439481738103784587339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11905626321158735856391559 17858439481738103784587339)
              ·
                refine ⟨26787659222607155676881009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17858439481738103784587339 26787659222607155676881009)
                ·
                  refine ⟨20090744416955366757660757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26787659222607155676881009 20090744416955366757660757)
                  ·
                    refine ⟨235438411136195704191337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 20090744416955366757660757 235438411136195704191337)
                    ·
                      refine ⟨176578808352146778143503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235438411136195704191337 176578808352146778143503)
                      ·
                        rfl

theorem cell23_343886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2].length) (baseStart_343886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343886 prefixEnd_343886 := by exact prefixLift 343886
  have htrace : WordTrace (prefixWord ++ tailWord_343886) baseStart_343886 baseEnd_343886 := by
    simpa [prefixWord, tailWord_343886, baseEnd_343886] using wordTrace_append hprefix tailTrace_343886
  have hstable : (prefixWord ++ tailWord_343886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343886).length < 2 ^ (prefixWord ++ tailWord_343886).sum := by decide
  have hdescent : baseEnd_343886 < baseStart_343886 := by decide
  rcases family_descends (prefixWord ++ tailWord_343886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343903 : List Nat := [1, 1, 2, 3, 1, 4, 3, 1, 1, 4, 2]
def baseStart_343903 : Nat := 118140960795 + 343903 * 2 ^ 59
def prefixEnd_343903 : Nat := 4983230072969 + 3 ^ 40 * 343903 * 2
def baseEnd_343903 : Nat := 176587537523273211630925

theorem tailTrace_343903 : CollatzResearch.WordTrace tailWord_343903 prefixEnd_343903 176587537523273211630925 := by
  unfold tailWord_343903
  simp only [CollatzResearch.WordTrace]
  refine ⟨12543172873105639801460363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8362115248737093200973575 12543172873105639801460363)
  ·
    refine ⟨18814759309658459702190545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12543172873105639801460363 18814759309658459702190545)
    ·
      refine ⟨14111069482243844776642909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18814759309658459702190545 14111069482243844776642909)
      ·
        refine ⟨5291651055841441791241091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14111069482243844776642909 5291651055841441791241091)
        ·
          refine ⟨7937476583762162686861637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5291651055841441791241091 7937476583762162686861637)
          ·
            refine ⟨1488276859455405503786557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7937476583762162686861637 1488276859455405503786557)
            ·
              refine ⟨558103822295777063919959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1488276859455405503786557 558103822295777063919959)
              ·
                refine ⟨837155733443665595879939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558103822295777063919959 837155733443665595879939)
                ·
                  refine ⟨1255733600165498393819909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 837155733443665595879939 1255733600165498393819909)
                  ·
                    refine ⟨235450050031030948841233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1255733600165498393819909 235450050031030948841233)
                    ·
                      refine ⟨176587537523273211630925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235450050031030948841233 176587537523273211630925)
                      ·
                        rfl

theorem cell23_343903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_343903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343903 prefixEnd_343903 := by exact prefixLift 343903
  have htrace : WordTrace (prefixWord ++ tailWord_343903) baseStart_343903 baseEnd_343903 := by
    simpa [prefixWord, tailWord_343903, baseEnd_343903] using wordTrace_append hprefix tailTrace_343903
  have hstable : (prefixWord ++ tailWord_343903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343903).length < 2 ^ (prefixWord ++ tailWord_343903).sum := by decide
  have hdescent : baseEnd_343903 < baseStart_343903 := by decide
  rcases family_descends (prefixWord ++ tailWord_343903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343943 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 7]
def baseStart_343943 : Nat := 118140960795 + 343943 * 2 ^ 59
def prefixEnd_343943 : Nat := 4983230072969 + 3 ^ 40 * 343943 * 2
def baseEnd_343943 : Nat := 19623119638828117236749

theorem tailTrace_343943 : CollatzResearch.WordTrace tailWord_343943 prefixEnd_343943 19623119638828117236749 := by
  unfold tailWord_343943
  simp only [CollatzResearch.WordTrace]
  refine ⟨12544631792960726632916483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8363087861973817755277655 12544631792960726632916483)
  ·
    refine ⟨18816947689441089949374725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12544631792960726632916483 18816947689441089949374725)
    ·
      refine ⟨3528177691770204365507761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18816947689441089949374725 3528177691770204365507761)
      ·
        refine ⟨2646133268827653274130821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3528177691770204365507761 2646133268827653274130821)
        ·
          refine ⟨496149987905184988899529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2646133268827653274130821 496149987905184988899529)
          ·
            refine ⟨372112490928888741674647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496149987905184988899529 372112490928888741674647)
            ·
              refine ⟨558168736393333112511971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372112490928888741674647 558168736393333112511971)
              ·
                refine ⟨837253104589999668767957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558168736393333112511971 837253104589999668767957)
                ·
                  refine ⟨19623119638828117236749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 837253104589999668767957 19623119638828117236749)
                  ·
                    rfl

theorem cell23_343943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 7].length) (baseStart_343943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343943 prefixEnd_343943 := by exact prefixLift 343943
  have htrace : WordTrace (prefixWord ++ tailWord_343943) baseStart_343943 baseEnd_343943 := by
    simpa [prefixWord, tailWord_343943, baseEnd_343943] using wordTrace_append hprefix tailTrace_343943
  have hstable : (prefixWord ++ tailWord_343943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343943).length < 2 ^ (prefixWord ++ tailWord_343943).sum := by decide
  have hdescent : baseEnd_343943 < baseStart_343943 := by decide
  rcases family_descends (prefixWord ++ tailWord_343943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343954 : List Nat := [3, 2, 3, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_343954 : Nat := 118140960795 + 343954 * 2 ^ 59
def prefixEnd_343954 : Nat := 4983230072969 + 3 ^ 40 * 343954 * 2
def baseEnd_343954 : Nat := 176613725036652512093191

theorem tailTrace_343954 : CollatzResearch.WordTrace tailWord_343954 prefixEnd_343954 176613725036652512093191 := by
  unfold tailWord_343954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3136258248980218877891729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8363355330613917007711277 3136258248980218877891729)
  ·
    refine ⟨2352193686735164158418797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3136258248980218877891729 2352193686735164158418797)
    ·
      refine ⟨882072632525686559407049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2352193686735164158418797 882072632525686559407049)
      ·
        refine ⟨661554474394264919555287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 882072632525686559407049 661554474394264919555287)
        ·
          refine ⟨992331711591397379332931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 661554474394264919555287 992331711591397379332931)
          ·
            refine ⟨1488497567387096068999397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 992331711591397379332931 1488497567387096068999397)
            ·
              refine ⟨279093293885080512937387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1488497567387096068999397 279093293885080512937387)
              ·
                refine ⟨418639940827620769406081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279093293885080512937387 418639940827620769406081)
                ·
                  refine ⟨313979955620715577054561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418639940827620769406081 313979955620715577054561)
                  ·
                    refine ⟨235484966715536682790921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 313979955620715577054561 235484966715536682790921)
                    ·
                      refine ⟨176613725036652512093191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235484966715536682790921 176613725036652512093191)
                      ·
                        rfl

theorem cell23_343954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_343954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343954 prefixEnd_343954 := by exact prefixLift 343954
  have htrace : WordTrace (prefixWord ++ tailWord_343954) baseStart_343954 baseEnd_343954 := by
    simpa [prefixWord, tailWord_343954, baseEnd_343954] using wordTrace_append hprefix tailTrace_343954
  have hstable : (prefixWord ++ tailWord_343954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343954).length < 2 ^ (prefixWord ++ tailWord_343954).sum := by decide
  have hdescent : baseEnd_343954 < baseStart_343954 := by decide
  rcases family_descends (prefixWord ++ tailWord_343954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343958 : List Nat := [5, 3, 1, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_343958 : Nat := 118140960795 + 343958 * 2 ^ 59
def prefixEnd_343958 : Nat := 4983230072969 + 3 ^ 40 * 343958 * 2
def baseEnd_343958 : Nat := 176615778959270496443173

theorem tailTrace_343958 : CollatzResearch.WordTrace tailWord_343958 prefixEnd_343958 176615778959270496443173 := by
  unfold tailWord_343958
  simp only [CollatzResearch.WordTrace]
  refine ⟨784073680494149012169533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8363452591937589463141685 784073680494149012169533)
  ·
    refine ⟨294027630185305879563575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 784073680494149012169533 294027630185305879563575)
    ·
      refine ⟨441041445277958819345363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294027630185305879563575 441041445277958819345363)
      ·
        refine ⟨661562167916938229018045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441041445277958819345363 661562167916938229018045)
        ·
          refine ⟨248085812968851835881767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 661562167916938229018045 248085812968851835881767)
          ·
            refine ⟨372128719453277753822651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248085812968851835881767 372128719453277753822651)
            ·
              refine ⟨558193079179916630733977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372128719453277753822651 558193079179916630733977)
              ·
                refine ⟨418644809384937473050483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558193079179916630733977 418644809384937473050483)
                ·
                  refine ⟨627967214077406209575725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 418644809384937473050483 627967214077406209575725)
                  ·
                    refine ⟨235487705279027328590897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 627967214077406209575725 235487705279027328590897)
                    ·
                      refine ⟨176615778959270496443173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235487705279027328590897 176615778959270496443173)
                      ·
                        rfl

theorem cell23_343958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_343958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343958 prefixEnd_343958 := by exact prefixLift 343958
  have htrace : WordTrace (prefixWord ++ tailWord_343958) baseStart_343958 baseEnd_343958 := by
    simpa [prefixWord, tailWord_343958, baseEnd_343958] using wordTrace_append hprefix tailTrace_343958
  have hstable : (prefixWord ++ tailWord_343958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343958).length < 2 ^ (prefixWord ++ tailWord_343958).sum := by decide
  have hdescent : baseEnd_343958 < baseStart_343958 := by decide
  rcases family_descends (prefixWord ++ tailWord_343958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343979 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 5]
def baseStart_343979 : Nat := 118140960795 + 343979 * 2 ^ 59
def prefixEnd_343979 : Nat := 4983230072969 + 3 ^ 40 * 343979 * 2
def baseEnd_343979 : Nat := 176626562053014914280575

theorem tailTrace_343979 : CollatzResearch.WordTrace tailWord_343979 prefixEnd_343979 176626562053014914280575 := by
  unfold tailWord_343979
  simp only [CollatzResearch.WordTrace]
  refine ⟨12545944820830304781226991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8363963213886869854151327 12545944820830304781226991)
  ·
    refine ⟨18818917231245457171840487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12545944820830304781226991 18818917231245457171840487)
    ·
      refine ⟨28228375846868185757760731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18818917231245457171840487 28228375846868185757760731)
      ·
        refine ⟨42342563770302278636641097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28228375846868185757760731 42342563770302278636641097)
        ·
          refine ⟨31756922827726708977480823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42342563770302278636641097 31756922827726708977480823)
          ·
            refine ⟨47635384241590063466221235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31756922827726708977480823 47635384241590063466221235)
            ·
              refine ⟨71453076362385095199331853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47635384241590063466221235 71453076362385095199331853)
              ·
                refine ⟨26794903635894410699749445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71453076362385095199331853 26794903635894410699749445)
                ·
                  refine ⟨5024044431730202006203021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26794903635894410699749445 5024044431730202006203021)
                  ·
                    refine ⟨1884016661898825752326133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5024044431730202006203021 1884016661898825752326133)
                    ·
                      refine ⟨176626562053014914280575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1884016661898825752326133 176626562053014914280575)
                      ·
                        rfl

theorem cell23_343979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 5].length) (baseStart_343979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343979 prefixEnd_343979 := by exact prefixLift 343979
  have htrace : WordTrace (prefixWord ++ tailWord_343979) baseStart_343979 baseEnd_343979 := by
    simpa [prefixWord, tailWord_343979, baseEnd_343979] using wordTrace_append hprefix tailTrace_343979
  have hstable : (prefixWord ++ tailWord_343979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343979).length < 2 ^ (prefixWord ++ tailWord_343979).sum := by decide
  have hdescent : baseEnd_343979 < baseStart_343979 := by decide
  rcases family_descends (prefixWord ++ tailWord_343979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343993 : List Nat := [1, 2, 1, 4, 2, 1, 2, 2, 2, 4, 2]
def baseStart_343993 : Nat := 118140960795 + 343993 * 2 ^ 59
def prefixEnd_343993 : Nat := 4983230072969 + 3 ^ 40 * 343993 * 2
def baseEnd_343993 : Nat := 176633750782177859505511

theorem tailTrace_343993 : CollatzResearch.WordTrace tailWord_343993 prefixEnd_343993 176633750782177859505511 := by
  unfold tailWord_343993
  simp only [CollatzResearch.WordTrace]
  refine ⟨12546455442779585172236633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8364303628519723448157755 12546455442779585172236633)
  ·
    refine ⟨9409841582084688879177475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12546455442779585172236633 9409841582084688879177475)
    ·
      refine ⟨14114762373127033318766213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9409841582084688879177475 14114762373127033318766213)
      ·
        refine ⟨2646517944961318747268665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14114762373127033318766213 2646517944961318747268665)
        ·
          refine ⟨1984888458720989060451499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2646517944961318747268665 1984888458720989060451499)
          ·
            refine ⟨2977332688081483590677249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1984888458720989060451499 2977332688081483590677249)
            ·
              refine ⟨2232999516061112693007937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2977332688081483590677249 2232999516061112693007937)
              ·
                refine ⟨1674749637045834519755953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2232999516061112693007937 1674749637045834519755953)
                ·
                  refine ⟨1256062227784375889816965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1674749637045834519755953 1256062227784375889816965)
                  ·
                    refine ⟨235511667709570479340681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1256062227784375889816965 235511667709570479340681)
                    ·
                      refine ⟨176633750782177859505511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235511667709570479340681 176633750782177859505511)
                      ·
                        rfl

theorem cell23_343993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 4, 2].length) (baseStart_343993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_343993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_343993 prefixEnd_343993 := by exact prefixLift 343993
  have htrace : WordTrace (prefixWord ++ tailWord_343993) baseStart_343993 baseEnd_343993 := by
    simpa [prefixWord, tailWord_343993, baseEnd_343993] using wordTrace_append hprefix tailTrace_343993
  have hstable : (prefixWord ++ tailWord_343993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343993).length < 2 ^ (prefixWord ++ tailWord_343993).sum := by decide
  have hdescent : baseEnd_343993 < baseStart_343993 := by decide
  rcases family_descends (prefixWord ++ tailWord_343993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344016 : List Nat := [2, 1, 1, 1, 1, 2, 6, 3, 6]
def baseStart_344016 : Nat := 118140960795 + 344016 * 2 ^ 59
def prefixEnd_344016 : Nat := 4983230072969 + 3 ^ 40 * 344016 * 2
def baseEnd_344016 : Nat := 19627284537470141057545

theorem tailTrace_344016 : CollatzResearch.WordTrace tailWord_344016 prefixEnd_344016 19627284537470141057545 := by
  unfold tailWord_344016
  simp only [CollatzResearch.WordTrace]
  refine ⟨6273647160848130050161951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8364862881130840066882601 6273647160848130050161951)
  ·
    refine ⟨9410470741272195075242927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6273647160848130050161951 9410470741272195075242927)
    ·
      refine ⟨14115706111908292612864391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9410470741272195075242927 14115706111908292612864391)
      ·
        refine ⟨21173559167862438919296587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14115706111908292612864391 21173559167862438919296587)
        ·
          refine ⟨31760338751793658378944881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21173559167862438919296587 31760338751793658378944881)
          ·
            refine ⟨23820254063845243784208661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31760338751793658378944881 23820254063845243784208661)
            ·
              refine ⟨1116574409242745802384781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23820254063845243784208661 1116574409242745802384781)
              ·
                refine ⟨418715403466029675894293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1116574409242745802384781 418715403466029675894293)
                ·
                  refine ⟨19627284537470141057545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 418715403466029675894293 19627284537470141057545)
                  ·
                    rfl

theorem cell23_344016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 6].length) (baseStart_344016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344016 prefixEnd_344016 := by exact prefixLift 344016
  have htrace : WordTrace (prefixWord ++ tailWord_344016) baseStart_344016 baseEnd_344016 := by
    simpa [prefixWord, tailWord_344016, baseEnd_344016] using wordTrace_append hprefix tailTrace_344016
  have hstable : (prefixWord ++ tailWord_344016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344016).length < 2 ^ (prefixWord ++ tailWord_344016).sum := by decide
  have hdescent : baseEnd_344016 < baseStart_344016 := by decide
  rcases family_descends (prefixWord ++ tailWord_344016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344060 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 3, 1, 3]
def baseStart_344060 : Nat := 118140960795 + 344060 * 2 ^ 59
def prefixEnd_344060 : Nat := 4983230072969 + 3 ^ 40 * 344060 * 2
def baseEnd_344060 : Nat := 176668153986029097367703

theorem tailTrace_344060 : CollatzResearch.WordTrace tailWord_344060 prefixEnd_344060 176668153986029097367703 := by
  unfold tailWord_344060
  simp only [CollatzResearch.WordTrace]
  refine ⟨6274449566768427807462817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8365932755691237076617089 6274449566768427807462817)
  ·
    refine ⟨4705837175076320855597113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6274449566768427807462817 4705837175076320855597113)
    ·
      refine ⟨3529377881307240641697835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4705837175076320855597113 3529377881307240641697835)
      ·
        refine ⟨5294066821960860962546753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3529377881307240641697835 5294066821960860962546753)
        ·
          refine ⟨3970550116470645721910065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5294066821960860962546753 3970550116470645721910065)
          ·
            refine ⟨2977912587352984291432549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3970550116470645721910065 2977912587352984291432549)
            ·
              refine ⟨558358610128684554643603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2977912587352984291432549 558358610128684554643603)
              ·
                refine ⟨837537915193026831965405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558358610128684554643603 837537915193026831965405)
                ·
                  refine ⟨314076718197385061987027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837537915193026831965405 314076718197385061987027)
                  ·
                    refine ⟨471115077296077592980541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 314076718197385061987027 471115077296077592980541)
                    ·
                      refine ⟨176668153986029097367703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 471115077296077592980541 176668153986029097367703)
                      ·
                        rfl

theorem cell23_344060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_344060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344060 prefixEnd_344060 := by exact prefixLift 344060
  have htrace : WordTrace (prefixWord ++ tailWord_344060) baseStart_344060 baseEnd_344060 := by
    simpa [prefixWord, tailWord_344060, baseEnd_344060] using wordTrace_append hprefix tailTrace_344060
  have hstable : (prefixWord ++ tailWord_344060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344060).length < 2 ^ (prefixWord ++ tailWord_344060).sum := by decide
  have hdescent : baseEnd_344060 < baseStart_344060 := by decide
  rcases family_descends (prefixWord ++ tailWord_344060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344083 : List Nat := [1, 1, 1, 2, 1, 4, 3, 4, 1, 1, 4]
def baseStart_344083 : Nat := 118140960795 + 344083 * 2 ^ 59
def prefixEnd_344083 : Nat := 4983230072969 + 3 ^ 40 * 344083 * 2
def baseEnd_344083 : Nat := 176679964041082507380097

theorem tailTrace_344083 : CollatzResearch.WordTrace tailWord_344083 prefixEnd_344083 176679964041082507380097 := by
  unfold tailWord_344083
  simp only [CollatzResearch.WordTrace]
  refine ⟨12549738012453530543012903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8366492008302353695341935 12549738012453530543012903)
  ·
    refine ⟨18824607018680295814519355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12549738012453530543012903 18824607018680295814519355)
    ·
      refine ⟨28236910528020443721779033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18824607018680295814519355 28236910528020443721779033)
      ·
        refine ⟨21177682896015332791334275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28236910528020443721779033 21177682896015332791334275)
        ·
          refine ⟨31766524344022999187001413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21177682896015332791334275 31766524344022999187001413)
          ·
            refine ⟨5956223314504312347562765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31766524344022999187001413 5956223314504312347562765)
            ·
              refine ⟨2233583742939117130336037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5956223314504312347562765 2233583742939117130336037)
              ·
                refine ⟨418796951801084461938007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2233583742939117130336037 418796951801084461938007)
                ·
                  refine ⟨628195427701626692907011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 418796951801084461938007 628195427701626692907011)
                  ·
                    refine ⟨942293141552440039360517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 628195427701626692907011 942293141552440039360517)
                    ·
                      refine ⟨176679964041082507380097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 942293141552440039360517 176679964041082507380097)
                      ·
                        rfl

theorem cell23_344083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 1, 4].length) (baseStart_344083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344083 prefixEnd_344083 := by exact prefixLift 344083
  have htrace : WordTrace (prefixWord ++ tailWord_344083) baseStart_344083 baseEnd_344083 := by
    simpa [prefixWord, tailWord_344083, baseEnd_344083] using wordTrace_append hprefix tailTrace_344083
  have hstable : (prefixWord ++ tailWord_344083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344083).length < 2 ^ (prefixWord ++ tailWord_344083).sum := by decide
  have hdescent : baseEnd_344083 < baseStart_344083 := by decide
  rcases family_descends (prefixWord ++ tailWord_344083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344104 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 2, 3, 2]
def baseStart_344104 : Nat := 118140960795 + 344104 * 2 ^ 59
def prefixEnd_344104 : Nat := 4983230072969 + 3 ^ 40 * 344104 * 2
def baseEnd_344104 : Nat := 176690747134826925217501

theorem tailTrace_344104 : CollatzResearch.WordTrace tailWord_344104 prefixEnd_344104 176690747134826925217501 := by
  unfold tailWord_344104
  simp only [CollatzResearch.WordTrace]
  refine ⟨6275251972688725564763683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8367002630251634086351577 6275251972688725564763683)
  ·
    refine ⟨9412877959033088347145525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6275251972688725564763683 9412877959033088347145525)
    ·
      refine ⟨882457308659352032544893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9412877959033088347145525 882457308659352032544893)
      ·
        refine ⟨330921490747257012204335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 882457308659352032544893 330921490747257012204335)
        ·
          refine ⟨496382236120885518306503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330921490747257012204335 496382236120885518306503)
          ·
            refine ⟨744573354181328277459755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496382236120885518306503 744573354181328277459755)
            ·
              refine ⟨1116860031271992416189633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 744573354181328277459755 1116860031271992416189633)
              ·
                refine ⟨837645023453994312142225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1116860031271992416189633 837645023453994312142225)
                ·
                  refine ⟨628233767590495734106669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 837645023453994312142225 628233767590495734106669)
                  ·
                    refine ⟨235587662846435900290001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 628233767590495734106669 235587662846435900290001)
                    ·
                      refine ⟨176690747134826925217501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235587662846435900290001 176690747134826925217501)
                      ·
                        rfl

theorem cell23_344104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_344104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344104 prefixEnd_344104 := by exact prefixLift 344104
  have htrace : WordTrace (prefixWord ++ tailWord_344104) baseStart_344104 baseEnd_344104 := by
    simpa [prefixWord, tailWord_344104, baseEnd_344104] using wordTrace_append hprefix tailTrace_344104
  have hstable : (prefixWord ++ tailWord_344104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344104).length < 2 ^ (prefixWord ++ tailWord_344104).sum := by decide
  have hdescent : baseEnd_344104 < baseStart_344104 := by decide
  rcases family_descends (prefixWord ++ tailWord_344104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344110 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 4, 4]
def baseStart_344110 : Nat := 118140960795 + 344110 * 2 ^ 59
def prefixEnd_344110 : Nat := 4983230072969 + 3 ^ 40 * 344110 * 2
def baseEnd_344110 : Nat := 58897942672917967247491

theorem tailTrace_344110 : CollatzResearch.WordTrace tailWord_344110 prefixEnd_344110 58897942672917967247491 := by
  unfold tailWord_344110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1568840347919464269280723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8367148522237142769497189 1568840347919464269280723)
  ·
    refine ⟨2353260521879196403921085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1568840347919464269280723 2353260521879196403921085)
    ·
      refine ⟨882472695704698651470407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2353260521879196403921085 882472695704698651470407)
      ·
        refine ⟨1323709043557047977205611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 882472695704698651470407 1323709043557047977205611)
        ·
          refine ⟨1985563565335571965808417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1323709043557047977205611 1985563565335571965808417)
          ·
            refine ⟨1489172674001678974356313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1985563565335571965808417 1489172674001678974356313)
            ·
              refine ⟨1116879505501259230767235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1489172674001678974356313 1116879505501259230767235)
              ·
                refine ⟨1675319258251888846150853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1116879505501259230767235 1675319258251888846150853)
                ·
                  refine ⟨314122360922229158653285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1675319258251888846150853 314122360922229158653285)
                  ·
                    refine ⟨58897942672917967247491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 314122360922229158653285 58897942672917967247491)
                    ·
                      rfl

theorem cell23_344110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_344110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344110 prefixEnd_344110 := by exact prefixLift 344110
  have htrace : WordTrace (prefixWord ++ tailWord_344110) baseStart_344110 baseEnd_344110 := by
    simpa [prefixWord, tailWord_344110, baseEnd_344110] using wordTrace_append hprefix tailTrace_344110
  have hstable : (prefixWord ++ tailWord_344110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344110).length < 2 ^ (prefixWord ++ tailWord_344110).sum := by decide
  have hdescent : baseEnd_344110 < baseStart_344110 := by decide
  rcases family_descends (prefixWord ++ tailWord_344110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344117 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 3, 2, 2]
def baseStart_344117 : Nat := 118140960795 + 344117 * 2 ^ 59
def prefixEnd_344117 : Nat := 4983230072969 + 3 ^ 40 * 344117 * 2
def baseEnd_344117 : Nat := 176697422383335374354941

theorem tailTrace_344117 : CollatzResearch.WordTrace tailWord_344117 prefixEnd_344117 176697422383335374354941 := by
  unfold tailWord_344117
  simp only [CollatzResearch.WordTrace]
  refine ⟨12550978094330354349750605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8367318729553569566500403 12550978094330354349750605)
  ·
    refine ⟨4706616785373882881156477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12550978094330354349750605 4706616785373882881156477)
    ·
      refine ⟨1764981294515206080433679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4706616785373882881156477 1764981294515206080433679)
      ·
        refine ⟨2647471941772809120650519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1764981294515206080433679 2647471941772809120650519)
        ·
          refine ⟨3971207912659213680975779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2647471941772809120650519 3971207912659213680975779)
          ·
            refine ⟨5956811868988820521463669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3971207912659213680975779 5956811868988820521463669)
            ·
              refine ⟨558451112717701923887219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5956811868988820521463669 558451112717701923887219)
              ·
                refine ⟨837676669076552885830829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558451112717701923887219 837676669076552885830829)
                ·
                  refine ⟨314128750903707332186561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 837676669076552885830829 314128750903707332186561)
                  ·
                    refine ⟨235596563177780499139921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 314128750903707332186561 235596563177780499139921)
                    ·
                      refine ⟨176697422383335374354941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235596563177780499139921 176697422383335374354941)
                      ·
                        rfl

theorem cell23_344117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_344117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344117 prefixEnd_344117 := by exact prefixLift 344117
  have htrace : WordTrace (prefixWord ++ tailWord_344117) baseStart_344117 baseEnd_344117 := by
    simpa [prefixWord, tailWord_344117, baseEnd_344117] using wordTrace_append hprefix tailTrace_344117
  have hstable : (prefixWord ++ tailWord_344117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344117).length < 2 ^ (prefixWord ++ tailWord_344117).sum := by decide
  have hdescent : baseEnd_344117 < baseStart_344117 := by decide
  rcases family_descends (prefixWord ++ tailWord_344117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344133 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 1, 3, 3]
def baseStart_344133 : Nat := 118140960795 + 344133 * 2 ^ 59
def prefixEnd_344133 : Nat := 4983230072969 + 3 ^ 40 * 344133 * 2
def baseEnd_344133 : Nat := 176705638073807311754867

theorem tailTrace_344133 : CollatzResearch.WordTrace tailWord_344133 prefixEnd_344133 176705638073807311754867 := by
  unfold tailWord_344133
  simp only [CollatzResearch.WordTrace]
  refine ⟨12551561662272389082333053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8367707774848259388222035 12551561662272389082333053)
  ·
    refine ⟨4706835623352145905874895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12551561662272389082333053 4706835623352145905874895)
    ·
      refine ⟨7060253435028218858812343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4706835623352145905874895 7060253435028218858812343)
      ·
        refine ⟨10590380152542328288218515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7060253435028218858812343 10590380152542328288218515)
        ·
          refine ⟨15885570228813492432327773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10590380152542328288218515 15885570228813492432327773)
          ·
            refine ⟨5957088835805059662122915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15885570228813492432327773 5957088835805059662122915)
            ·
              refine ⟨8935633253707589493184373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5957088835805059662122915 8935633253707589493184373)
              ·
                refine ⟨837715617535086514986035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8935633253707589493184373 837715617535086514986035)
                ·
                  refine ⟨1256573426302629772479053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 837715617535086514986035 1256573426302629772479053)
                  ·
                    refine ⟨471215034863486164679645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1256573426302629772479053 471215034863486164679645)
                    ·
                      refine ⟨176705638073807311754867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 471215034863486164679645 176705638073807311754867)
                      ·
                        rfl

theorem cell23_344133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_344133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344133 prefixEnd_344133 := by exact prefixLift 344133
  have htrace : WordTrace (prefixWord ++ tailWord_344133) baseStart_344133 baseEnd_344133 := by
    simpa [prefixWord, tailWord_344133, baseEnd_344133] using wordTrace_append hprefix tailTrace_344133
  have hstable : (prefixWord ++ tailWord_344133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344133).length < 2 ^ (prefixWord ++ tailWord_344133).sum := by decide
  have hdescent : baseEnd_344133 < baseStart_344133 := by decide
  rcases family_descends (prefixWord ++ tailWord_344133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344134 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_344134 : Nat := 118140960795 + 344134 * 2 ^ 59
def prefixEnd_344134 : Nat := 4983230072969 + 3 ^ 40 * 344134 * 2
def baseEnd_344134 : Nat := 176706151554461807842363

theorem tailTrace_344134 : CollatzResearch.WordTrace tailWord_344134 prefixEnd_344134 176706151554461807842363 := by
  unfold tailWord_344134
  simp only [CollatzResearch.WordTrace]
  refine ⟨392237441727148945409983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8367732090179177502079637 392237441727148945409983)
  ·
    refine ⟨588356162590723418114975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 392237441727148945409983 588356162590723418114975)
    ·
      refine ⟨882534243886085127172463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 588356162590723418114975 882534243886085127172463)
      ·
        refine ⟨1323801365829127690758695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 882534243886085127172463 1323801365829127690758695)
        ·
          refine ⟨1985702048743691536138043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1323801365829127690758695 1985702048743691536138043)
          ·
            refine ⟨2978553073115537304207065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1985702048743691536138043 2978553073115537304207065)
            ·
              refine ⟨2233914804836652978155299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2978553073115537304207065 2233914804836652978155299)
              ·
                refine ⟨3350872207254979467232949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2233914804836652978155299 3350872207254979467232949)
                ·
                  refine ⟨314144269430154325053089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3350872207254979467232949 314144269430154325053089)
                  ·
                    refine ⟨235608202072615743789817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 314144269430154325053089 235608202072615743789817)
                    ·
                      refine ⟨176706151554461807842363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235608202072615743789817 176706151554461807842363)
                      ·
                        rfl

theorem cell23_344134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_344134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344134 prefixEnd_344134 := by exact prefixLift 344134
  have htrace : WordTrace (prefixWord ++ tailWord_344134) baseStart_344134 baseEnd_344134 := by
    simpa [prefixWord, tailWord_344134, baseEnd_344134] using wordTrace_append hprefix tailTrace_344134
  have hstable : (prefixWord ++ tailWord_344134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344134).length < 2 ^ (prefixWord ++ tailWord_344134).sum := by decide
  have hdescent : baseEnd_344134 < baseStart_344134 := by decide
  rcases family_descends (prefixWord ++ tailWord_344134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344136 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 4, 7]
def baseStart_344136 : Nat := 118140960795 + 344136 * 2 ^ 59
def prefixEnd_344136 : Nat := 4983230072969 + 3 ^ 40 * 344136 * 2
def baseEnd_344136 : Nat := 58902392838590266672451

theorem tailTrace_344136 : CollatzResearch.WordTrace tailWord_344136 prefixEnd_344136 58902392838590266672451 := by
  unfold tailWord_344136
  simp only [CollatzResearch.WordTrace]
  refine ⟨6275835540630760297346131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8367780720841013729794841 6275835540630760297346131)
  ·
    refine ⟨9413753310946140446019197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6275835540630760297346131 9413753310946140446019197)
    ·
      refine ⟨3530157491604802667257199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9413753310946140446019197 3530157491604802667257199)
      ·
        refine ⟨5295236237407204000885799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3530157491604802667257199 5295236237407204000885799)
        ·
          refine ⟨7942854356110806001328699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5295236237407204000885799 7942854356110806001328699)
          ·
            refine ⟨11914281534166209001993049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7942854356110806001328699 11914281534166209001993049)
            ·
              refine ⟨8935711150624656751494787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11914281534166209001993049 8935711150624656751494787)
              ·
                refine ⟨13403566725936985127242181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8935711150624656751494787 13403566725936985127242181)
                ·
                  refine ⟨2513168761113184711357909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13403566725936985127242181 2513168761113184711357909)
                  ·
                    refine ⟨58902392838590266672451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2513168761113184711357909 58902392838590266672451)
                    ·
                      rfl

theorem cell23_344136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_344136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344136 prefixEnd_344136 := by exact prefixLift 344136
  have htrace : WordTrace (prefixWord ++ tailWord_344136) baseStart_344136 baseEnd_344136 := by
    simpa [prefixWord, tailWord_344136, baseEnd_344136] using wordTrace_append hprefix tailTrace_344136
  have hstable : (prefixWord ++ tailWord_344136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344136).length < 2 ^ (prefixWord ++ tailWord_344136).sum := by decide
  have hdescent : baseEnd_344136 < baseStart_344136 := by decide
  rcases family_descends (prefixWord ++ tailWord_344136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344143 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 2, 7, 2]
def baseStart_344143 : Nat := 118140960795 + 344143 * 2 ^ 59
def prefixEnd_344143 : Nat := 4983230072969 + 3 ^ 40 * 344143 * 2
def baseEnd_344143 : Nat := 176710772880352272629821

theorem tailTrace_344143 : CollatzResearch.WordTrace tailWord_344143 prefixEnd_344143 176710772880352272629821 := by
  unfold tailWord_344143
  simp only [CollatzResearch.WordTrace]
  refine ⟨12551926392236160790197083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8367950928157440526798055 12551926392236160790197083)
  ·
    refine ⟨18827889588354241185295625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12551926392236160790197083 18827889588354241185295625)
    ·
      refine ⟨14120917191265680888971719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18827889588354241185295625 14120917191265680888971719)
      ·
        refine ⟨21181375786898521333457579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14120917191265680888971719 21181375786898521333457579)
        ·
          refine ⟨31772063680347782000186369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21181375786898521333457579 31772063680347782000186369)
          ·
            refine ⟨23829047760260836500139777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31772063680347782000186369 23829047760260836500139777)
            ·
              refine ⟨17871785820195627375104833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23829047760260836500139777 17871785820195627375104833)
              ·
                refine ⟨13403839365146720531328625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17871785820195627375104833 13403839365146720531328625)
                ·
                  refine ⟨10052879523860040398496469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13403839365146720531328625 10052879523860040398496469)
                  ·
                    refine ⟨235614363840469696839761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10052879523860040398496469 235614363840469696839761)
                    ·
                      refine ⟨176710772880352272629821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235614363840469696839761 176710772880352272629821)
                      ·
                        rfl

theorem cell23_344143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 7, 2].length) (baseStart_344143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344143 prefixEnd_344143 := by exact prefixLift 344143
  have htrace : WordTrace (prefixWord ++ tailWord_344143) baseStart_344143 baseEnd_344143 := by
    simpa [prefixWord, tailWord_344143, baseEnd_344143] using wordTrace_append hprefix tailTrace_344143
  have hstable : (prefixWord ++ tailWord_344143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344143).length < 2 ^ (prefixWord ++ tailWord_344143).sum := by decide
  have hdescent : baseEnd_344143 < baseStart_344143 := by decide
  rcases family_descends (prefixWord ++ tailWord_344143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344167 : List Nat := [1, 1, 5, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_344167 : Nat := 118140960795 + 344167 * 2 ^ 59
def prefixEnd_344167 : Nat := 4983230072969 + 3 ^ 40 * 344167 * 2
def baseEnd_344167 : Nat := 176723096416060178729711

theorem tailTrace_344167 : CollatzResearch.WordTrace tailWord_344167 prefixEnd_344167 176723096416060178729711 := by
  unfold tailWord_344167
  simp only [CollatzResearch.WordTrace]
  refine ⟨12552801744149212889070755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8368534496099475259380503 12552801744149212889070755)
  ·
    refine ⟨18829202616223819333606133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12552801744149212889070755 18829202616223819333606133)
    ·
      refine ⟨1765237745270983062525575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18829202616223819333606133 1765237745270983062525575)
      ·
        refine ⟨2647856617906474593788363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1765237745270983062525575 2647856617906474593788363)
        ·
          refine ⟨3971784926859711890682545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2647856617906474593788363 3971784926859711890682545)
          ·
            refine ⟨2978838695144783918011909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3971784926859711890682545 2978838695144783918011909)
            ·
              refine ⟨558532255339646984627233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2978838695144783918011909 558532255339646984627233)
              ·
                refine ⟨418899191504735238470425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558532255339646984627233 418899191504735238470425)
                ·
                  refine ⟨314174393628551428852819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418899191504735238470425 314174393628551428852819)
                  ·
                    refine ⟨471261590442827143279229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 314174393628551428852819 471261590442827143279229)
                    ·
                      refine ⟨176723096416060178729711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 471261590442827143279229 176723096416060178729711)
                      ·
                        rfl

theorem cell23_344167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_344167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344167 prefixEnd_344167 := by exact prefixLift 344167
  have htrace : WordTrace (prefixWord ++ tailWord_344167) baseStart_344167 baseEnd_344167 := by
    simpa [prefixWord, tailWord_344167, baseEnd_344167] using wordTrace_append hprefix tailTrace_344167
  have hstable : (prefixWord ++ tailWord_344167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344167).length < 2 ^ (prefixWord ++ tailWord_344167).sum := by decide
  have hdescent : baseEnd_344167 < baseStart_344167 := by decide
  rcases family_descends (prefixWord ++ tailWord_344167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344173 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 1, 5, 4]
def baseStart_344173 : Nat := 118140960795 + 344173 * 2 ^ 59
def prefixEnd_344173 : Nat := 4983230072969 + 3 ^ 40 * 344173 * 2
def baseEnd_344173 : Nat := 176726177299987155254683

theorem tailTrace_344173 : CollatzResearch.WordTrace tailWord_344173 prefixEnd_344173 176726177299987155254683 := by
  unfold tailWord_344173
  simp only [CollatzResearch.WordTrace]
  refine ⟨12553020582127475913789173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8368680388084983942526115 12553020582127475913789173)
  ·
    refine ⟨1176845679574450866917735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12553020582127475913789173 1176845679574450866917735)
    ·
      refine ⟨1765268519361676300376603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1176845679574450866917735 1765268519361676300376603)
      ·
        refine ⟨2647902779042514450564905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1765268519361676300376603 2647902779042514450564905)
        ·
          refine ⟨1985927084281885837923679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2647902779042514450564905 1985927084281885837923679)
          ·
            refine ⟨2978890626422828756885519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1985927084281885837923679 2978890626422828756885519)
            ·
              refine ⟨4468335939634243135328279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2978890626422828756885519 4468335939634243135328279)
              ·
                refine ⟨6702503909451364702992419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4468335939634243135328279 6702503909451364702992419)
                ·
                  refine ⟨10053755864177047054488629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6702503909451364702992419 10053755864177047054488629)
                  ·
                    refine ⟨942539612266598161358309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10053755864177047054488629 942539612266598161358309)
                    ·
                      refine ⟨176726177299987155254683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 942539612266598161358309 176726177299987155254683)
                      ·
                        rfl

theorem cell23_344173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_344173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344173 prefixEnd_344173 := by exact prefixLift 344173
  have htrace : WordTrace (prefixWord ++ tailWord_344173) baseStart_344173 baseEnd_344173 := by
    simpa [prefixWord, tailWord_344173, baseEnd_344173] using wordTrace_append hprefix tailTrace_344173
  have hstable : (prefixWord ++ tailWord_344173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344173).length < 2 ^ (prefixWord ++ tailWord_344173).sum := by decide
  have hdescent : baseEnd_344173 < baseStart_344173 := by decide
  rcases family_descends (prefixWord ++ tailWord_344173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344183 : List Nat := [1, 1, 3, 1, 1, 6, 1, 1, 2, 6]
def baseStart_344183 : Nat := 118140960795 + 344183 * 2 ^ 59
def prefixEnd_344183 : Nat := 4983230072969 + 3 ^ 40 * 344183 * 2
def baseEnd_344183 : Nat := 58910437368844038709879

theorem tailTrace_344183 : CollatzResearch.WordTrace tailWord_344183 prefixEnd_344183 58910437368844038709879 := by
  unfold tailWord_344183
  simp only [CollatzResearch.WordTrace]
  refine ⟨12553385312091247621653203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8368923541394165081102135 12553385312091247621653203)
  ·
    refine ⟨18830077968136871432479805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12553385312091247621653203 18830077968136871432479805)
    ·
      refine ⟨7061279238051326787179927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18830077968136871432479805 7061279238051326787179927)
      ·
        refine ⟨10591918857076990180769891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7061279238051326787179927 10591918857076990180769891)
        ·
          refine ⟨15887878285615485271154837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10591918857076990180769891 15887878285615485271154837)
          ·
            refine ⟨744744294638225872085383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15887878285615485271154837 744744294638225872085383)
            ·
              refine ⟨1117116441957338808128075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 744744294638225872085383 1117116441957338808128075)
              ·
                refine ⟨1675674662936008212192113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117116441957338808128075 1675674662936008212192113)
                ·
                  refine ⟨1256755997202006159144085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1675674662936008212192113 1256755997202006159144085)
                  ·
                    refine ⟨58910437368844038709879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1256755997202006159144085 58910437368844038709879)
                    ·
                      rfl

theorem cell23_344183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_344183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344183 prefixEnd_344183 := by exact prefixLift 344183
  have htrace : WordTrace (prefixWord ++ tailWord_344183) baseStart_344183 baseEnd_344183 := by
    simpa [prefixWord, tailWord_344183, baseEnd_344183] using wordTrace_append hprefix tailTrace_344183
  have hstable : (prefixWord ++ tailWord_344183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344183).length < 2 ^ (prefixWord ++ tailWord_344183).sum := by decide
  have hdescent : baseEnd_344183 < baseStart_344183 := by decide
  rcases family_descends (prefixWord ++ tailWord_344183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344224 : List Nat := [2, 1, 1, 4, 2, 2, 3, 2, 2, 2, 2]
def baseStart_344224 : Nat := 118140960795 + 344224 * 2 ^ 59
def prefixEnd_344224 : Nat := 4983230072969 + 3 ^ 40 * 344224 * 2
def baseEnd_344224 : Nat := 176752364813366455716949

theorem tailTrace_344224 : CollatzResearch.WordTrace tailWord_344224 prefixEnd_344224 176752364813366455716949 := by
  unfold tailWord_344224
  simp only [CollatzResearch.WordTrace]
  refine ⟨6277440352471355811947863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8369920469961807749263817 6277440352471355811947863)
  ·
    refine ⟨9416160528707033717921795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6277440352471355811947863 9416160528707033717921795)
    ·
      refine ⟨14124240793060550576882693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9416160528707033717921795 14124240793060550576882693)
      ·
        refine ⟨2648295148698853233165505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14124240793060550576882693 2648295148698853233165505)
        ·
          refine ⟨1986221361524139924874129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2648295148698853233165505 1986221361524139924874129)
          ·
            refine ⟨1489666021143104943655597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1986221361524139924874129 1489666021143104943655597)
            ·
              refine ⟨558624757928664353870849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1489666021143104943655597 558624757928664353870849)
              ·
                refine ⟨418968568446498265403137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558624757928664353870849 418968568446498265403137)
                ·
                  refine ⟨314226426334873699052353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 418968568446498265403137 314226426334873699052353)
                  ·
                    refine ⟨235669819751155274289265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 314226426334873699052353 235669819751155274289265)
                    ·
                      refine ⟨176752364813366455716949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235669819751155274289265 176752364813366455716949)
                      ·
                        rfl

theorem cell23_344224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_344224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344224 prefixEnd_344224 := by exact prefixLift 344224
  have htrace : WordTrace (prefixWord ++ tailWord_344224) baseStart_344224 baseEnd_344224 := by
    simpa [prefixWord, tailWord_344224, baseEnd_344224] using wordTrace_append hprefix tailTrace_344224
  have hstable : (prefixWord ++ tailWord_344224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344224).length < 2 ^ (prefixWord ++ tailWord_344224).sum := by decide
  have hdescent : baseEnd_344224 < baseStart_344224 := by decide
  rcases family_descends (prefixWord ++ tailWord_344224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344241 : List Nat := [1, 2, 2, 5, 3, 1, 1, 1, 1, 4, 2]
def baseStart_344241 : Nat := 118140960795 + 344241 * 2 ^ 59
def prefixEnd_344241 : Nat := 4983230072969 + 3 ^ 40 * 344241 * 2
def baseEnd_344241 : Nat := 176761093984492889204371

theorem tailTrace_344241 : CollatzResearch.WordTrace tailWord_344241 prefixEnd_344241 176761093984492889204371 := by
  unfold tailWord_344241
  simp only [CollatzResearch.WordTrace]
  refine ⟨12555500745881123527264577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8370333830587415684843051 12555500745881123527264577)
  ·
    refine ⟨9416625559410842645448433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12555500745881123527264577 9416625559410842645448433)
    ·
      refine ⟨7062469169558131984086325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9416625559410842645448433 7062469169558131984086325)
      ·
        refine ⟨662106484646074873508093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7062469169558131984086325 662106484646074873508093)
        ·
          refine ⟨248289931742278077565535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 662106484646074873508093 248289931742278077565535)
          ·
            refine ⟨372434897613417116348303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248289931742278077565535 372434897613417116348303)
            ·
              refine ⟨558652346420125674522455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372434897613417116348303 558652346420125674522455)
              ·
                refine ⟨837978519630188511783683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558652346420125674522455 837978519630188511783683)
                ·
                  refine ⟨1256967779445282767675525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 837978519630188511783683 1256967779445282767675525)
                  ·
                    refine ⟨235681458645990518939161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1256967779445282767675525 235681458645990518939161)
                    ·
                      refine ⟨176761093984492889204371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235681458645990518939161 176761093984492889204371)
                      ·
                        rfl

theorem cell23_344241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_344241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344241 prefixEnd_344241 := by exact prefixLift 344241
  have htrace : WordTrace (prefixWord ++ tailWord_344241) baseStart_344241 baseEnd_344241 := by
    simpa [prefixWord, tailWord_344241, baseEnd_344241] using wordTrace_append hprefix tailTrace_344241
  have hstable : (prefixWord ++ tailWord_344241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344241).length < 2 ^ (prefixWord ++ tailWord_344241).sum := by decide
  have hdescent : baseEnd_344241 < baseStart_344241 := by decide
  rcases family_descends (prefixWord ++ tailWord_344241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344250 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2]
def baseStart_344250 : Nat := 118140960795 + 344250 * 2 ^ 59
def prefixEnd_344250 : Nat := 4983230072969 + 3 ^ 40 * 344250 * 2
def baseEnd_344250 : Nat := 176765715310383353991829

theorem tailTrace_344250 : CollatzResearch.WordTrace tailWord_344250 prefixEnd_344250 176765715310383353991829 := by
  unfold tailWord_344250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3138957250712129516085551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8370552668565678709561469 3138957250712129516085551)
  ·
    refine ⟨4708435876068194274128327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3138957250712129516085551 4708435876068194274128327)
    ·
      refine ⟨7062653814102291411192491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4708435876068194274128327 7062653814102291411192491)
      ·
        refine ⟨10593980721153437116788737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7062653814102291411192491 10593980721153437116788737)
        ·
          refine ⟨7945485540865077837591553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10593980721153437116788737 7945485540865077837591553)
          ·
            refine ⟨5959114155648808378193665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7945485540865077837591553 5959114155648808378193665)
            ·
              refine ⟨4469335616736606283645249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5959114155648808378193665 4469335616736606283645249)
              ·
                refine ⟨3352001712552454712733937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4469335616736606283645249 3352001712552454712733937)
                ·
                  refine ⟨2514001284414341034550453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3352001712552454712733937 2514001284414341034550453)
                  ·
                    refine ⟨235687620413844471989105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2514001284414341034550453 235687620413844471989105)
                    ·
                      refine ⟨176765715310383353991829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235687620413844471989105 176765715310383353991829)
                      ·
                        rfl

theorem cell23_344250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2].length) (baseStart_344250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344250 prefixEnd_344250 := by exact prefixLift 344250
  have htrace : WordTrace (prefixWord ++ tailWord_344250) baseStart_344250 baseEnd_344250 := by
    simpa [prefixWord, tailWord_344250, baseEnd_344250] using wordTrace_append hprefix tailTrace_344250
  have hstable : (prefixWord ++ tailWord_344250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344250).length < 2 ^ (prefixWord ++ tailWord_344250).sum := by decide
  have hdescent : baseEnd_344250 < baseStart_344250 := by decide
  rcases family_descends (prefixWord ++ tailWord_344250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344253 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_344253 : Nat := 118140960795 + 344253 * 2 ^ 59
def prefixEnd_344253 : Nat := 4983230072969 + 3 ^ 40 * 344253 * 2
def baseEnd_344253 : Nat := 176767255752346842254315

theorem tailTrace_344253 : CollatzResearch.WordTrace tailWord_344253 prefixEnd_344253 176767255752346842254315 := by
  unfold tailWord_344253
  simp only [CollatzResearch.WordTrace]
  refine ⟨12555938421837649576701413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8370625614558433051134275 12555938421837649576701413)
  ·
    refine ⟨2354238454094559295631515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12555938421837649576701413 2354238454094559295631515)
    ·
      refine ⟨3531357681141838943447273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2354238454094559295631515 3531357681141838943447273)
      ·
        refine ⟨2648518260856379207585455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3531357681141838943447273 2648518260856379207585455)
        ·
          refine ⟨3972777391284568811378183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2648518260856379207585455 3972777391284568811378183)
          ·
            refine ⟨5959166086926853217067275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3972777391284568811378183 5959166086926853217067275)
            ·
              refine ⟨8938749130390279825600913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5959166086926853217067275 8938749130390279825600913)
              ·
                refine ⟨6704061847792709869200685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8938749130390279825600913 6704061847792709869200685)
                ·
                  refine ⟨2514023192922266200950257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6704061847792709869200685 2514023192922266200950257)
                  ·
                    refine ⟨1885517394691699650712693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2514023192922266200950257 1885517394691699650712693)
                    ·
                      refine ⟨176767255752346842254315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1885517394691699650712693 176767255752346842254315)
                      ·
                        rfl

theorem cell23_344253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_344253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344253 prefixEnd_344253 := by exact prefixLift 344253
  have htrace : WordTrace (prefixWord ++ tailWord_344253) baseStart_344253 baseEnd_344253 := by
    simpa [prefixWord, tailWord_344253, baseEnd_344253] using wordTrace_append hprefix tailTrace_344253
  have hstable : (prefixWord ++ tailWord_344253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344253).length < 2 ^ (prefixWord ++ tailWord_344253).sum := by decide
  have hdescent : baseEnd_344253 < baseStart_344253 := by decide
  rcases family_descends (prefixWord ++ tailWord_344253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344260 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 1, 7]
def baseStart_344260 : Nat := 118140960795 + 344260 * 2 ^ 59
def prefixEnd_344260 : Nat := 4983230072969 + 3 ^ 40 * 344260 * 2
def baseEnd_344260 : Nat := 58923616705642771622261

theorem tailTrace_344260 : CollatzResearch.WordTrace tailWord_344260 prefixEnd_344260 58923616705642771622261 := by
  unfold tailWord_344260
  simp only [CollatzResearch.WordTrace]
  refine ⟨6278096866406144886103117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8370795821874859848137489 6278096866406144886103117)
  ·
    refine ⟨2354286324902304332288669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6278096866406144886103117 2354286324902304332288669)
    ·
      refine ⟨882857371838364124608251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2354286324902304332288669 882857371838364124608251)
      ·
        refine ⟨1324286057757546186912377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 882857371838364124608251 1324286057757546186912377)
        ·
          refine ⟨993214543318159640184283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1324286057757546186912377 993214543318159640184283)
          ·
            refine ⟨1489821814977239460276425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993214543318159640184283 1489821814977239460276425)
            ·
              refine ⟨1117366361232929595207319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1489821814977239460276425 1117366361232929595207319)
              ·
                refine ⟨1676049541849394392810979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117366361232929595207319 1676049541849394392810979)
                ·
                  refine ⟨2514074312774091589216469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676049541849394392810979 2514074312774091589216469)
                  ·
                    refine ⟨58923616705642771622261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2514074312774091589216469 58923616705642771622261)
                    ·
                      rfl

theorem cell23_344260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_344260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344260 prefixEnd_344260 := by exact prefixLift 344260
  have htrace : WordTrace (prefixWord ++ tailWord_344260) baseStart_344260 baseEnd_344260 := by
    simpa [prefixWord, tailWord_344260, baseEnd_344260] using wordTrace_append hprefix tailTrace_344260
  have hstable : (prefixWord ++ tailWord_344260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344260).length < 2 ^ (prefixWord ++ tailWord_344260).sum := by decide
  have hdescent : baseEnd_344260 < baseStart_344260 := by decide
  rcases family_descends (prefixWord ++ tailWord_344260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344277 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 2, 5]
def baseStart_344277 : Nat := 118140960795 + 344277 * 2 ^ 59
def prefixEnd_344277 : Nat := 4983230072969 + 3 ^ 40 * 344277 * 2
def baseEnd_344277 : Nat := 58926526429351582784735

theorem tailTrace_344277 : CollatzResearch.WordTrace tailWord_344277 prefixEnd_344277 58926526429351582784735 := by
  unfold tailWord_344277
  simp only [CollatzResearch.WordTrace]
  refine ⟨12556813773750701675575085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8371209182500467783716723 12556813773750701675575085)
  ·
    refine ⟨4708805165156513128340657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12556813773750701675575085 4708805165156513128340657)
    ·
      refine ⟨3531603873867384846255493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4708805165156513128340657 3531603873867384846255493)
      ·
        refine ⟨662175726350134658672905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3531603873867384846255493 662175726350134658672905)
        ·
          refine ⟨496631794762600994004679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 662175726350134658672905 496631794762600994004679)
          ·
            refine ⟨744947692143901491007019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496631794762600994004679 744947692143901491007019)
            ·
              refine ⟨1117421538215852236510529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 744947692143901491007019 1117421538215852236510529)
              ·
                refine ⟨838066153661889177382897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1117421538215852236510529 838066153661889177382897)
                ·
                  refine ⟨628549615246416883037173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 838066153661889177382897 628549615246416883037173)
                  ·
                    refine ⟨58926526429351582784735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 628549615246416883037173 58926526429351582784735)
                    ·
                      rfl

theorem cell23_344277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_344277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344277 prefixEnd_344277 := by exact prefixLift 344277
  have htrace : WordTrace (prefixWord ++ tailWord_344277) baseStart_344277 baseEnd_344277 := by
    simpa [prefixWord, tailWord_344277, baseEnd_344277] using wordTrace_append hprefix tailTrace_344277
  have hstable : (prefixWord ++ tailWord_344277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344277).length < 2 ^ (prefixWord ++ tailWord_344277).sum := by decide
  have hdescent : baseEnd_344277 < baseStart_344277 := by decide
  rcases family_descends (prefixWord ++ tailWord_344277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344280 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 4, 1, 4]
def baseStart_344280 : Nat := 118140960795 + 344280 * 2 ^ 59
def prefixEnd_344280 : Nat := 4983230072969 + 3 ^ 40 * 344280 * 2
def baseEnd_344280 : Nat := 176781119730018236616691

theorem tailTrace_344280 : CollatzResearch.WordTrace tailWord_344280 prefixEnd_344280 176781119730018236616691 := by
  unfold tailWord_344280
  simp only [CollatzResearch.WordTrace]
  refine ⟨6278461596369916593967147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8371282128493222125289529 6278461596369916593967147)
  ·
    refine ⟨9417692394554874890950721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6278461596369916593967147 9417692394554874890950721)
    ·
      refine ⟨7063269295916156168213041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9417692394554874890950721 7063269295916156168213041)
      ·
        refine ⟨5297451971937117126159781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7063269295916156168213041 5297451971937117126159781)
        ·
          refine ⟨993272244738209461154959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5297451971937117126159781 993272244738209461154959)
          ·
            refine ⟨1489908367107314191732439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993272244738209461154959 1489908367107314191732439)
            ·
              refine ⟨2234862550660971287598659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1489908367107314191732439 2234862550660971287598659)
              ·
                refine ⟨3352293825991456931397989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2234862550660971287598659 3352293825991456931397989)
                ·
                  refine ⟨628555092373398174637123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3352293825991456931397989 628555092373398174637123)
                  ·
                    refine ⟨942832638560097261955685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 628555092373398174637123 942832638560097261955685)
                    ·
                      refine ⟨176781119730018236616691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 942832638560097261955685 176781119730018236616691)
                      ·
                        rfl

theorem cell23_344280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_344280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344280 prefixEnd_344280 := by exact prefixLift 344280
  have htrace : WordTrace (prefixWord ++ tailWord_344280) baseStart_344280 baseEnd_344280 := by
    simpa [prefixWord, tailWord_344280, baseEnd_344280] using wordTrace_append hprefix tailTrace_344280
  have hstable : (prefixWord ++ tailWord_344280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344280).length < 2 ^ (prefixWord ++ tailWord_344280).sum := by decide
  have hdescent : baseEnd_344280 < baseStart_344280 := by decide
  rcases family_descends (prefixWord ++ tailWord_344280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344300 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 3]
def baseStart_344300 : Nat := 118140960795 + 344300 * 2 ^ 59
def prefixEnd_344300 : Nat := 4983230072969 + 3 ^ 40 * 344300 * 2
def baseEnd_344300 : Nat := 176791389343108158366599

theorem tailTrace_344300 : CollatzResearch.WordTrace tailWord_344300 prefixEnd_344300 176791389343108158366599 := by
  unfold tailWord_344300
  simp only [CollatzResearch.WordTrace]
  refine ⟨6278826326333688301831177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8371768435111584402441569 6278826326333688301831177)
  ·
    refine ⟨4709119744750266226373383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6278826326333688301831177 4709119744750266226373383)
    ·
      refine ⟨7063679617125399339560075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4709119744750266226373383 7063679617125399339560075)
      ·
        refine ⟨10595519425688099009340113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7063679617125399339560075 10595519425688099009340113)
        ·
          refine ⟨7946639569266074257005085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10595519425688099009340113 7946639569266074257005085)
          ·
            refine ⟨2979989838474777846376907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7946639569266074257005085 2979989838474777846376907)
            ·
              refine ⟨4469984757712166769565361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2979989838474777846376907 4469984757712166769565361)
              ·
                refine ⟨3352488568284125077174021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4469984757712166769565361 3352488568284125077174021)
                ·
                  refine ⟨628591606553273451970129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3352488568284125077174021 628591606553273451970129)
                  ·
                    refine ⟨471443704914955088977597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 628591606553273451970129 471443704914955088977597)
                    ·
                      refine ⟨176791389343108158366599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 471443704914955088977597 176791389343108158366599)
                      ·
                        rfl

theorem cell23_344300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_344300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344300 prefixEnd_344300 := by exact prefixLift 344300
  have htrace : WordTrace (prefixWord ++ tailWord_344300) baseStart_344300 baseEnd_344300 := by
    simpa [prefixWord, tailWord_344300, baseEnd_344300] using wordTrace_append hprefix tailTrace_344300
  have hstable : (prefixWord ++ tailWord_344300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344300).length < 2 ^ (prefixWord ++ tailWord_344300).sum := by decide
  have hdescent : baseEnd_344300 < baseStart_344300 := by decide
  rcases family_descends (prefixWord ++ tailWord_344300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344310 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4]
def baseStart_344310 : Nat := 118140960795 + 344310 * 2 ^ 59
def prefixEnd_344310 : Nat := 4983230072969 + 3 ^ 40 * 344310 * 2
def baseEnd_344310 : Nat := 176796524149653119241553

theorem tailTrace_344310 : CollatzResearch.WordTrace tailWord_344310 prefixEnd_344310 176796524149653119241553 := by
  unfold tailWord_344310
  simp only [CollatzResearch.WordTrace]
  refine ⟨784876086414446769470399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8372011588420765541017589 784876086414446769470399)
  ·
    refine ⟨1177314129621670154205599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 784876086414446769470399 1177314129621670154205599)
    ·
      refine ⟨1765971194432505231308399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1177314129621670154205599 1765971194432505231308399)
      ·
        refine ⟨2648956791648757846962599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1765971194432505231308399 2648956791648757846962599)
        ·
          refine ⟨3973435187473136770443899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2648956791648757846962599 3973435187473136770443899)
          ·
            refine ⟨5960152781209705155665849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3973435187473136770443899 5960152781209705155665849)
            ·
              refine ⟨4470114585907278866749387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5960152781209705155665849 4470114585907278866749387)
              ·
                refine ⟨6705171878860918300124081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4470114585907278866749387 6705171878860918300124081)
                ·
                  refine ⟨5028878909145688725093061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6705171878860918300124081 5028878909145688725093061)
                  ·
                    refine ⟨942914795464816635954949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5028878909145688725093061 942914795464816635954949)
                    ·
                      refine ⟨176796524149653119241553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 942914795464816635954949 176796524149653119241553)
                      ·
                        rfl

theorem cell23_344310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_344310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344310 prefixEnd_344310 := by exact prefixLift 344310
  have htrace : WordTrace (prefixWord ++ tailWord_344310) baseStart_344310 baseEnd_344310 := by
    simpa [prefixWord, tailWord_344310, baseEnd_344310] using wordTrace_append hprefix tailTrace_344310
  have hstable : (prefixWord ++ tailWord_344310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344310).length < 2 ^ (prefixWord ++ tailWord_344310).sum := by decide
  have hdescent : baseEnd_344310 < baseStart_344310 := by decide
  rcases family_descends (prefixWord ++ tailWord_344310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344380 : List Nat := [2, 2, 2, 2, 1, 2, 1, 4, 1, 6]
def baseStart_344380 : Nat := 118140960795 + 344380 * 2 ^ 59
def prefixEnd_344380 : Nat := 4983230072969 + 3 ^ 40 * 344380 * 2
def baseEnd_344380 : Nat := 58944155931822615122077

theorem tailTrace_344380 : CollatzResearch.WordTrace tailWord_344380 prefixEnd_344380 58944155931822615122077 := by
  unfold tailWord_344380
  simp only [CollatzResearch.WordTrace]
  refine ⟨6280285246188775133287297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8373713661585033511049729 6280285246188775133287297)
  ·
    refine ⟨4710213934641581349965473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6280285246188775133287297 4710213934641581349965473)
    ·
      refine ⟨3532660450981186012474105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4710213934641581349965473 3532660450981186012474105)
      ·
        refine ⟨2649495338235889509355579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3532660450981186012474105 2649495338235889509355579)
        ·
          refine ⟨3974243007353834264033369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2649495338235889509355579 3974243007353834264033369)
          ·
            refine ⟨2980682255515375698025027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3974243007353834264033369 2980682255515375698025027)
            ·
              refine ⟨4471023383273063547037541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2980682255515375698025027 4471023383273063547037541)
              ·
                refine ⟨838316884363699415069539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4471023383273063547037541 838316884363699415069539)
                ·
                  refine ⟨1257475326545549122604309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 838316884363699415069539 1257475326545549122604309)
                  ·
                    refine ⟨58944155931822615122077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1257475326545549122604309 58944155931822615122077)
                    ·
                      rfl

theorem cell23_344380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_344380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344380 prefixEnd_344380 := by exact prefixLift 344380
  have htrace : WordTrace (prefixWord ++ tailWord_344380) baseStart_344380 baseEnd_344380 := by
    simpa [prefixWord, tailWord_344380, baseEnd_344380] using wordTrace_append hprefix tailTrace_344380
  have hstable : (prefixWord ++ tailWord_344380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344380).length < 2 ^ (prefixWord ++ tailWord_344380).sum := by decide
  have hdescent : baseEnd_344380 < baseStart_344380 := by decide
  rcases family_descends (prefixWord ++ tailWord_344380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344424 : List Nat := [2, 1, 4, 2, 2, 1, 1, 4, 1, 2, 3]
def baseStart_344424 : Nat := 118140960795 + 344424 * 2 ^ 59
def prefixEnd_344424 : Nat := 4983230072969 + 3 ^ 40 * 344424 * 2
def baseEnd_344424 : Nat := 176855060944265673216029

theorem tailTrace_344424 : CollatzResearch.WordTrace tailWord_344424 prefixEnd_344424 176855060944265673216029 := by
  unfold tailWord_344424
  simp only [CollatzResearch.WordTrace]
  refine ⟨6281087652109072890588163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8374783536145430520784217 6281087652109072890588163)
  ·
    refine ⟨9421631478163609335882245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6281087652109072890588163 9421631478163609335882245)
    ·
      refine ⟨1766555902155676750477921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9421631478163609335882245 1766555902155676750477921)
      ·
        refine ⟨1324916926616757562858441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1766555902155676750477921 1324916926616757562858441)
        ·
          refine ⟨993687694962568172143831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1324916926616757562858441 993687694962568172143831)
          ·
            refine ⟨1490531542443852258215747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993687694962568172143831 1490531542443852258215747)
            ·
              refine ⟨2235797313665778387323621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1490531542443852258215747 2235797313665778387323621)
              ·
                refine ⟨419211996312333447623179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2235797313665778387323621 419211996312333447623179)
                ·
                  refine ⟨628817994468500171434769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419211996312333447623179 628817994468500171434769)
                  ·
                    refine ⟨471613495851375128576077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 628817994468500171434769 471613495851375128576077)
                    ·
                      refine ⟨176855060944265673216029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 471613495851375128576077 176855060944265673216029)
                      ·
                        rfl

theorem cell23_344424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_344424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344424 prefixEnd_344424 := by exact prefixLift 344424
  have htrace : WordTrace (prefixWord ++ tailWord_344424) baseStart_344424 baseEnd_344424 := by
    simpa [prefixWord, tailWord_344424, baseEnd_344424] using wordTrace_append hprefix tailTrace_344424
  have hstable : (prefixWord ++ tailWord_344424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344424).length < 2 ^ (prefixWord ++ tailWord_344424).sum := by decide
  have hdescent : baseEnd_344424 < baseStart_344424 := by decide
  rcases family_descends (prefixWord ++ tailWord_344424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344471 : List Nat := [1, 1, 3, 3, 1, 1, 6, 1, 2, 1, 3]
def baseStart_344471 : Nat := 118140960795 + 344471 * 2 ^ 59
def prefixEnd_344471 : Nat := 4983230072969 + 3 ^ 40 * 344471 * 2
def baseEnd_344471 : Nat := 176879194535026989328313

theorem tailTrace_344471 : CollatzResearch.WordTrace tailWord_344471 prefixEnd_344471 176879194535026989328313 := by
  unfold tailWord_344471
  simp only [CollatzResearch.WordTrace]
  refine ⟨12563889535047872808137267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8375926356698581872091511 12563889535047872808137267)
  ·
    refine ⟨18845834302571809212205901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12563889535047872808137267 18845834302571809212205901)
    ·
      refine ⟨7067187863464428454577213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18845834302571809212205901 7067187863464428454577213)
      ·
        refine ⟨2650195448799160670466455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7067187863464428454577213 2650195448799160670466455)
        ·
          refine ⟨3975293173198741005699683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2650195448799160670466455 3975293173198741005699683)
          ·
            refine ⟨5962939759798111508549525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3975293173198741005699683 5962939759798111508549525)
            ·
              refine ⟨279512801240536476963259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5962939759798111508549525 279512801240536476963259)
              ·
                refine ⟨419269201860804715444889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279512801240536476963259 419269201860804715444889)
                ·
                  refine ⟨314451901395603536583667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 419269201860804715444889 314451901395603536583667)
                  ·
                    refine ⟨471677852093405304875501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 314451901395603536583667 471677852093405304875501)
                    ·
                      refine ⟨176879194535026989328313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 471677852093405304875501 176879194535026989328313)
                      ·
                        rfl

theorem cell23_344471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_344471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344471 prefixEnd_344471 := by exact prefixLift 344471
  have htrace : WordTrace (prefixWord ++ tailWord_344471) baseStart_344471 baseEnd_344471 := by
    simpa [prefixWord, tailWord_344471, baseEnd_344471] using wordTrace_append hprefix tailTrace_344471
  have hstable : (prefixWord ++ tailWord_344471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344471).length < 2 ^ (prefixWord ++ tailWord_344471).sum := by decide
  have hdescent : baseEnd_344471 < baseStart_344471 := by decide
  rcases family_descends (prefixWord ++ tailWord_344471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344497 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 2, 1, 5]
def baseStart_344497 : Nat := 118140960795 + 344497 * 2 ^ 59
def prefixEnd_344497 : Nat := 4983230072969 + 3 ^ 40 * 344497 * 2
def baseEnd_344497 : Nat := 176892545032043887603193

theorem tailTrace_344497 : CollatzResearch.WordTrace tailWord_344497 prefixEnd_344497 176892545032043887603193 := by
  unfold tailWord_344497
  simp only [CollatzResearch.WordTrace]
  refine ⟨12564837832953679248583745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8376558555302452832389163 12564837832953679248583745)
  ·
    refine ⟨9423628374715259436437809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12564837832953679248583745 9423628374715259436437809)
    ·
      refine ⟨7067721281036444577328357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9423628374715259436437809 7067721281036444577328357)
      ·
        refine ⟨1325197740194333358249067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7067721281036444577328357 1325197740194333358249067)
        ·
          refine ⟨1987796610291500037373601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1325197740194333358249067 1987796610291500037373601)
          ·
            refine ⟨1490847457718625028030201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1987796610291500037373601 1490847457718625028030201)
            ·
              refine ⟨1118135593288968771022651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1490847457718625028030201 1118135593288968771022651)
              ·
                refine ⟨1677203389933453156533977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118135593288968771022651 1677203389933453156533977)
                ·
                  refine ⟨1257902542450089867400483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1677203389933453156533977 1257902542450089867400483)
                  ·
                    refine ⟨1886853813675134801100725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1257902542450089867400483 1886853813675134801100725)
                    ·
                      refine ⟨176892545032043887603193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1886853813675134801100725 176892545032043887603193)
                      ·
                        rfl

theorem cell23_344497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_344497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344497 prefixEnd_344497 := by exact prefixLift 344497
  have htrace : WordTrace (prefixWord ++ tailWord_344497) baseStart_344497 baseEnd_344497 := by
    simpa [prefixWord, tailWord_344497, baseEnd_344497] using wordTrace_append hprefix tailTrace_344497
  have hstable : (prefixWord ++ tailWord_344497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344497).length < 2 ^ (prefixWord ++ tailWord_344497).sum := by decide
  have hdescent : baseEnd_344497 < baseStart_344497 := by decide
  rcases family_descends (prefixWord ++ tailWord_344497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344524 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 2, 2, 4]
def baseStart_344524 : Nat := 118140960795 + 344524 * 2 ^ 59
def prefixEnd_344524 : Nat := 4983230072969 + 3 ^ 40 * 344524 * 2
def baseEnd_344524 : Nat := 176906409009715281965569

theorem tailTrace_344524 : CollatzResearch.WordTrace tailWord_344524 prefixEnd_344524 176906409009715281965569 := by
  unfold tailWord_344524
  simp only [CollatzResearch.WordTrace]
  refine ⟨6282911301927931429908313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8377215069237241906544417 6282911301927931429908313)
  ·
    refine ⟨4712183476445948572431235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6282911301927931429908313 4712183476445948572431235)
    ·
      refine ⟨7068275214668922858646853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4712183476445948572431235 7068275214668922858646853)
      ·
        refine ⟨1325301602750423035996285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7068275214668922858646853 1325301602750423035996285)
        ·
          refine ⟨496988101031408638498607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1325301602750423035996285 496988101031408638498607)
          ·
            refine ⟨745482151547112957747911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496988101031408638498607 745482151547112957747911)
            ·
              refine ⟨1118223227320669436621867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745482151547112957747911 1118223227320669436621867)
              ·
                refine ⟨1677334840981004154932801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118223227320669436621867 1677334840981004154932801)
                ·
                  refine ⟨1258001130735753116199601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1677334840981004154932801 1258001130735753116199601)
                  ·
                    refine ⟨943500848051814837149701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1258001130735753116199601 943500848051814837149701)
                    ·
                      refine ⟨176906409009715281965569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 943500848051814837149701 176906409009715281965569)
                      ·
                        rfl

theorem cell23_344524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_344524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344524 prefixEnd_344524 := by exact prefixLift 344524
  have htrace : WordTrace (prefixWord ++ tailWord_344524) baseStart_344524 baseEnd_344524 := by
    simpa [prefixWord, tailWord_344524, baseEnd_344524] using wordTrace_append hprefix tailTrace_344524
  have hstable : (prefixWord ++ tailWord_344524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344524).length < 2 ^ (prefixWord ++ tailWord_344524).sum := by decide
  have hdescent : baseEnd_344524 < baseStart_344524 := by decide
  rcases family_descends (prefixWord ++ tailWord_344524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344534 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 7]
def baseStart_344534 : Nat := 118140960795 + 344534 * 2 ^ 59
def prefixEnd_344534 : Nat := 4983230072969 + 3 ^ 40 * 344534 * 2
def baseEnd_344534 : Nat := 19656838201806693648947

theorem tailTrace_344534 : CollatzResearch.WordTrace tailWord_344534 prefixEnd_344534 19656838201806693648947 := by
  unfold tailWord_344534
  simp only [CollatzResearch.WordTrace]
  refine ⟨785386708363727160480041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8377458222546423045120437 785386708363727160480041)
  ·
    refine ⟨589040031272795370360031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 785386708363727160480041 589040031272795370360031)
    ·
      refine ⟨883560046909193055540047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 589040031272795370360031 883560046909193055540047)
      ·
        refine ⟨1325340070363789583310071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 883560046909193055540047 1325340070363789583310071)
        ·
          refine ⟨1988010105545684374965107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1325340070363789583310071 1988010105545684374965107)
          ·
            refine ⟨2982015158318526562447661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988010105545684374965107 2982015158318526562447661)
            ·
              refine ⟨1118255684369447460917873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2982015158318526562447661 1118255684369447460917873)
              ·
                refine ⟨838691763277085595688405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1118255684369447460917873 838691763277085595688405)
                ·
                  refine ⟨19656838201806693648947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 838691763277085595688405 19656838201806693648947)
                  ·
                    rfl

theorem cell23_344534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_344534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344534 prefixEnd_344534 := by exact prefixLift 344534
  have htrace : WordTrace (prefixWord ++ tailWord_344534) baseStart_344534 baseEnd_344534 := by
    simpa [prefixWord, tailWord_344534, baseEnd_344534] using wordTrace_append hprefix tailTrace_344534
  have hstable : (prefixWord ++ tailWord_344534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344534).length < 2 ^ (prefixWord ++ tailWord_344534).sum := by decide
  have hdescent : baseEnd_344534 < baseStart_344534 := by decide
  rcases family_descends (prefixWord ++ tailWord_344534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344562 : List Nat := [3, 2, 1, 4, 3, 1, 1, 2, 2, 2, 2]
def baseStart_344562 : Nat := 118140960795 + 344562 * 2 ^ 59
def prefixEnd_344562 : Nat := 4983230072969 + 3 ^ 40 * 344562 * 2
def baseEnd_344562 : Nat := 176925921274586133290395

theorem tailTrace_344562 : CollatzResearch.WordTrace tailWord_344562 prefixEnd_344562 176925921274586133290395 := by
  unfold tailWord_344562
  simp only [CollatzResearch.WordTrace]
  refine ⟨3141802144429548837424985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8378139051812130233133293 3141802144429548837424985)
  ·
    refine ⟨2356351608322161628068739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3141802144429548837424985 2356351608322161628068739)
    ·
      refine ⟨3534527412483242442103109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2356351608322161628068739 3534527412483242442103109)
      ·
        refine ⟨662723889840607957894333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3534527412483242442103109 662723889840607957894333)
        ·
          refine ⟨248521458690227984210375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 662723889840607957894333 248521458690227984210375)
          ·
            refine ⟨372782188035341976315563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 248521458690227984210375 372782188035341976315563)
            ·
              refine ⟨559173282053012964473345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372782188035341976315563 559173282053012964473345)
              ·
                refine ⟨419379961539759723355009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 559173282053012964473345 419379961539759723355009)
                ·
                  refine ⟨314534971154819792516257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 419379961539759723355009 314534971154819792516257)
                  ·
                    refine ⟨235901228366114844387193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 314534971154819792516257 235901228366114844387193)
                    ·
                      refine ⟨176925921274586133290395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235901228366114844387193 176925921274586133290395)
                      ·
                        rfl

theorem cell23_344562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_344562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344562 prefixEnd_344562 := by exact prefixLift 344562
  have htrace : WordTrace (prefixWord ++ tailWord_344562) baseStart_344562 baseEnd_344562 := by
    simpa [prefixWord, tailWord_344562, baseEnd_344562] using wordTrace_append hprefix tailTrace_344562
  have hstable : (prefixWord ++ tailWord_344562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344562).length < 2 ^ (prefixWord ++ tailWord_344562).sum := by decide
  have hdescent : baseEnd_344562 < baseStart_344562 := by decide
  rcases family_descends (prefixWord ++ tailWord_344562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344597 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_344597 : Nat := 118140960795 + 344597 * 2 ^ 59
def prefixEnd_344597 : Nat := 4983230072969 + 3 ^ 40 * 344597 * 2
def baseEnd_344597 : Nat := 176943893097493496352733

theorem tailTrace_344597 : CollatzResearch.WordTrace tailWord_344597 prefixEnd_344597 176943893097493496352733 := by
  unfold tailWord_344597
  simp only [CollatzResearch.WordTrace]
  refine ⟨12568485132591396327224045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8378990088394264218149363 12568485132591396327224045)
  ·
    refine ⟨4713181924721773622709017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12568485132591396327224045 4713181924721773622709017)
    ·
      refine ⟨3534886443541330217031763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4713181924721773622709017 3534886443541330217031763)
      ·
        refine ⟨5302329665311995325547645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3534886443541330217031763 5302329665311995325547645)
        ·
          refine ⟨1988373624491998247080367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5302329665311995325547645 1988373624491998247080367)
          ·
            refine ⟨2982560436737997370620551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988373624491998247080367 2982560436737997370620551)
            ·
              refine ⟨4473840655106996055930827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2982560436737997370620551 4473840655106996055930827)
              ·
                refine ⟨6710760982660494083896241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4473840655106996055930827 6710760982660494083896241)
                ·
                  refine ⟨5033070736995370562922181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6710760982660494083896241 5033070736995370562922181)
                  ·
                    refine ⟨943700763186631980547909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5033070736995370562922181 943700763186631980547909)
                    ·
                      refine ⟨176943893097493496352733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 943700763186631980547909 176943893097493496352733)
                      ·
                        rfl

theorem cell23_344597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_344597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344597 prefixEnd_344597 := by exact prefixLift 344597
  have htrace : WordTrace (prefixWord ++ tailWord_344597) baseStart_344597 baseEnd_344597 := by
    simpa [prefixWord, tailWord_344597, baseEnd_344597] using wordTrace_append hprefix tailTrace_344597
  have hstable : (prefixWord ++ tailWord_344597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344597).length < 2 ^ (prefixWord ++ tailWord_344597).sum := by decide
  have hdescent : baseEnd_344597 < baseStart_344597 := by decide
  rcases family_descends (prefixWord ++ tailWord_344597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344604 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 1, 4, 3]
def baseStart_344604 : Nat := 118140960795 + 344604 * 2 ^ 59
def prefixEnd_344604 : Nat := 4983230072969 + 3 ^ 40 * 344604 * 2
def baseEnd_344604 : Nat := 176947487462074968965201

theorem tailTrace_344604 : CollatzResearch.WordTrace tailWord_344604 prefixEnd_344604 176947487462074968965201 := by
  unfold tailWord_344604
  simp only [CollatzResearch.WordTrace]
  refine ⟨6284370221783018261364433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8379160295710691015152577 6284370221783018261364433)
  ·
    refine ⟨4713277666337263696023325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6284370221783018261364433 4713277666337263696023325)
    ·
      refine ⟨1767479124876473886008747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4713277666337263696023325 1767479124876473886008747)
      ·
        refine ⟨2651218687314710829013121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1767479124876473886008747 2651218687314710829013121)
        ·
          refine ⟨1988414015486033121759841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2651218687314710829013121 1988414015486033121759841)
          ·
            refine ⟨1491310511614524841319881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1988414015486033121759841 1491310511614524841319881)
            ·
              refine ⟨1118482883710893630989911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1491310511614524841319881 1118482883710893630989911)
              ·
                refine ⟨1677724325566340446484867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118482883710893630989911 1677724325566340446484867)
                ·
                  refine ⟨2516586488349510669727301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677724325566340446484867 2516586488349510669727301)
                  ·
                    refine ⟨471859966565533250573869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2516586488349510669727301 471859966565533250573869)
                    ·
                      refine ⟨176947487462074968965201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 471859966565533250573869 176947487462074968965201)
                      ·
                        rfl

theorem cell23_344604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_344604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344604 prefixEnd_344604 := by exact prefixLift 344604
  have htrace : WordTrace (prefixWord ++ tailWord_344604) baseStart_344604 baseEnd_344604 := by
    simpa [prefixWord, tailWord_344604, baseEnd_344604] using wordTrace_append hprefix tailTrace_344604
  have hstable : (prefixWord ++ tailWord_344604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344604).length < 2 ^ (prefixWord ++ tailWord_344604).sum := by decide
  have hdescent : baseEnd_344604 < baseStart_344604 := by decide
  rcases family_descends (prefixWord ++ tailWord_344604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344641 : List Nat := [1, 2, 5, 1, 1, 2, 4, 1, 6]
def baseStart_344641 : Nat := 118140960795 + 344641 * 2 ^ 59
def prefixEnd_344641 : Nat := 4983230072969 + 3 ^ 40 * 344641 * 2
def baseEnd_344641 : Nat := 19662942916254591578059

theorem tailTrace_344641 : CollatzResearch.WordTrace tailWord_344641 prefixEnd_344641 19662942916254591578059 := by
  unfold tailWord_344641
  simp only [CollatzResearch.WordTrace]
  refine ⟨12570089944431991841825777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8380059962954661227883851 12570089944431991841825777)
  ·
    refine ⟨9427567458323993881369333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12570089944431991841825777 9427567458323993881369333)
    ·
      refine ⟨883834449217874426378375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9427567458323993881369333 883834449217874426378375)
      ·
        refine ⟨1325751673826811639567563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 883834449217874426378375 1325751673826811639567563)
        ·
          refine ⟨1988627510740217459351345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1325751673826811639567563 1988627510740217459351345)
          ·
            refine ⟨1491470633055163094513509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1988627510740217459351345 1491470633055163094513509)
            ·
              refine ⟨279650743697843080221283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1491470633055163094513509 279650743697843080221283)
              ·
                refine ⟨419476115546764620331925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279650743697843080221283 419476115546764620331925)
                ·
                  refine ⟨19662942916254591578059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 419476115546764620331925 19662942916254591578059)
                  ·
                    rfl

theorem cell23_344641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 6].length) (baseStart_344641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344641 prefixEnd_344641 := by exact prefixLift 344641
  have htrace : WordTrace (prefixWord ++ tailWord_344641) baseStart_344641 baseEnd_344641 := by
    simpa [prefixWord, tailWord_344641, baseEnd_344641] using wordTrace_append hprefix tailTrace_344641
  have hstable : (prefixWord ++ tailWord_344641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344641).length < 2 ^ (prefixWord ++ tailWord_344641).sum := by decide
  have hdescent : baseEnd_344641 < baseStart_344641 := by decide
  rcases family_descends (prefixWord ++ tailWord_344641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344661 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 2, 3, 2]
def baseStart_344661 : Nat := 118140960795 + 344661 * 2 ^ 59
def prefixEnd_344661 : Nat := 4983230072969 + 3 ^ 40 * 344661 * 2
def baseEnd_344661 : Nat := 176976755859381245952439

theorem tailTrace_344661 : CollatzResearch.WordTrace tailWord_344661 prefixEnd_344661 176976755859381245952439 := by
  unfold tailWord_344661
  simp only [CollatzResearch.WordTrace]
  refine ⟨12570819404359535257553837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8380546269573023505035891 12570819404359535257553837)
  ·
    refine ⟨4714057276634825721582689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12570819404359535257553837 4714057276634825721582689)
    ·
      refine ⟨3535542957476119291187017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4714057276634825721582689 3535542957476119291187017)
      ·
        refine ⟨2651657218107089468390263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3535542957476119291187017 2651657218107089468390263)
        ·
          refine ⟨3977485827160634202585395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2651657218107089468390263 3977485827160634202585395)
          ·
            refine ⟨5966228740740951303878093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3977485827160634202585395 5966228740740951303878093)
            ·
              refine ⟨2237335777777856738954285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5966228740740951303878093 2237335777777856738954285)
              ·
                refine ⟨839000916666696277107857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2237335777777856738954285 839000916666696277107857)
                ·
                  refine ⟨629250687500022207830893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 839000916666696277107857 629250687500022207830893)
                  ·
                    refine ⟨235969007812508327936585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 629250687500022207830893 235969007812508327936585)
                    ·
                      refine ⟨176976755859381245952439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 235969007812508327936585 176976755859381245952439)
                      ·
                        rfl

theorem cell23_344661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_344661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344661 prefixEnd_344661 := by exact prefixLift 344661
  have htrace : WordTrace (prefixWord ++ tailWord_344661) baseStart_344661 baseEnd_344661 := by
    simpa [prefixWord, tailWord_344661, baseEnd_344661] using wordTrace_append hprefix tailTrace_344661
  have hstable : (prefixWord ++ tailWord_344661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344661).length < 2 ^ (prefixWord ++ tailWord_344661).sum := by decide
  have hdescent : baseEnd_344661 < baseStart_344661 := by decide
  rcases family_descends (prefixWord ++ tailWord_344661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344684 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 4, 4]
def baseStart_344684 : Nat := 118140960795 + 344684 * 2 ^ 59
def prefixEnd_344684 : Nat := 4983230072969 + 3 ^ 40 * 344684 * 2
def baseEnd_344684 : Nat := 58996188638144885321611

theorem tailTrace_344684 : CollatzResearch.WordTrace tailWord_344684 prefixEnd_344684 58996188638144885321611 := by
  unfold tailWord_344684
  simp only [CollatzResearch.WordTrace]
  refine ⟨6285829141638105092820553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8381105522184140123760737 6285829141638105092820553)
  ·
    refine ⟨4714371856228578819615415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6285829141638105092820553 4714371856228578819615415)
    ·
      refine ⟨7071557784342868229423123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4714371856228578819615415 7071557784342868229423123)
      ·
        refine ⟨10607336676514302344134685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7071557784342868229423123 10607336676514302344134685)
        ·
          refine ⟨3977751253692863379050507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10607336676514302344134685 3977751253692863379050507)
          ·
            refine ⟨5966626880539295068575761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3977751253692863379050507 5966626880539295068575761)
            ·
              refine ⟨4474970160404471301431821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5966626880539295068575761 4474970160404471301431821)
              ·
                refine ⟨1678113810151676738036933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4474970160404471301431821 1678113810151676738036933)
                ·
                  refine ⟨314646339403439388381925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1678113810151676738036933 314646339403439388381925)
                  ·
                    refine ⟨58996188638144885321611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 314646339403439388381925 58996188638144885321611)
                    ·
                      rfl

theorem cell23_344684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_344684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344684 prefixEnd_344684 := by exact prefixLift 344684
  have htrace : WordTrace (prefixWord ++ tailWord_344684) baseStart_344684 baseEnd_344684 := by
    simpa [prefixWord, tailWord_344684, baseEnd_344684] using wordTrace_append hprefix tailTrace_344684
  have hstable : (prefixWord ++ tailWord_344684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344684).length < 2 ^ (prefixWord ++ tailWord_344684).sum := by decide
  have hdescent : baseEnd_344684 < baseStart_344684 := by decide
  rcases family_descends (prefixWord ++ tailWord_344684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344685 : List Nat := [1, 5, 1, 1, 3, 2, 1, 4, 1, 1, 3]
def baseStart_344685 : Nat := 118140960795 + 344685 * 2 ^ 59
def prefixEnd_344685 : Nat := 4983230072969 + 3 ^ 40 * 344685 * 2
def baseEnd_344685 : Nat := 176989079395089152052329

theorem tailTrace_344685 : CollatzResearch.WordTrace tailWord_344685 prefixEnd_344685 176989079395089152052329 := by
  unfold tailWord_344685
  simp only [CollatzResearch.WordTrace]
  refine ⟨12571694756272587356427509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8381129837515058237618339 12571694756272587356427509)
  ·
    refine ⟨1178596383400555064665079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12571694756272587356427509 1178596383400555064665079)
    ·
      refine ⟨1767894575100832596997619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1178596383400555064665079 1767894575100832596997619)
      ·
        refine ⟨2651841862651248895496429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1767894575100832596997619 2651841862651248895496429)
        ·
          refine ⟨994440698494218335811161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2651841862651248895496429 994440698494218335811161)
          ·
            refine ⟨745830523870663751858371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 994440698494218335811161 745830523870663751858371)
            ·
              refine ⟨1118745785805995627787557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745830523870663751858371 1118745785805995627787557)
              ·
                refine ⟨209764834838624180210167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1118745785805995627787557 209764834838624180210167)
                ·
                  refine ⟨314647252257936270315251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 209764834838624180210167 314647252257936270315251)
                  ·
                    refine ⟨471970878386904405472877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 314647252257936270315251 471970878386904405472877)
                    ·
                      refine ⟨176989079395089152052329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 471970878386904405472877 176989079395089152052329)
                      ·
                        rfl

theorem cell23_344685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_344685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344685 prefixEnd_344685 := by exact prefixLift 344685
  have htrace : WordTrace (prefixWord ++ tailWord_344685) baseStart_344685 baseEnd_344685 := by
    simpa [prefixWord, tailWord_344685, baseEnd_344685] using wordTrace_append hprefix tailTrace_344685
  have hstable : (prefixWord ++ tailWord_344685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344685).length < 2 ^ (prefixWord ++ tailWord_344685).sum := by decide
  have hdescent : baseEnd_344685 < baseStart_344685 := by decide
  rcases family_descends (prefixWord ++ tailWord_344685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344687 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 6]
def baseStart_344687 : Nat := 118140960795 + 344687 * 2 ^ 59
def prefixEnd_344687 : Nat := 4983230072969 + 3 ^ 40 * 344687 * 2
def baseEnd_344687 : Nat := 176990106356398144227319

theorem tailTrace_344687 : CollatzResearch.WordTrace tailWord_344687 prefixEnd_344687 176990106356398144227319 := by
  unfold tailWord_344687
  simp only [CollatzResearch.WordTrace]
  refine ⟨12571767702265341698000315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8381178468176894465333543 12571767702265341698000315)
  ·
    refine ⟨18857651553398012547000473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12571767702265341698000315 18857651553398012547000473)
    ·
      refine ⟨14143238665048509410250355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18857651553398012547000473 14143238665048509410250355)
      ·
        refine ⟨21214857997572764115375533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14143238665048509410250355 21214857997572764115375533)
        ·
          refine ⟨7955571749089786543265825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21214857997572764115375533 7955571749089786543265825)
          ·
            refine ⟨5966678811817339907449369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7955571749089786543265825 5966678811817339907449369)
            ·
              refine ⟨4475009108863004930587027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5966678811817339907449369 4475009108863004930587027)
              ·
                refine ⟨6712513663294507395880541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4475009108863004930587027 6712513663294507395880541)
                ·
                  refine ⟨2517192623735440273455203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6712513663294507395880541 2517192623735440273455203)
                  ·
                    refine ⟨3775788935603160410182805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2517192623735440273455203 3775788935603160410182805)
                    ·
                      refine ⟨176990106356398144227319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3775788935603160410182805 176990106356398144227319)
                      ·
                        rfl

theorem cell23_344687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_344687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344687 prefixEnd_344687 := by exact prefixLift 344687
  have htrace : WordTrace (prefixWord ++ tailWord_344687) baseStart_344687 baseEnd_344687 := by
    simpa [prefixWord, tailWord_344687, baseEnd_344687] using wordTrace_append hprefix tailTrace_344687
  have hstable : (prefixWord ++ tailWord_344687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344687).length < 2 ^ (prefixWord ++ tailWord_344687).sum := by decide
  have hdescent : baseEnd_344687 < baseStart_344687 := by decide
  rcases family_descends (prefixWord ++ tailWord_344687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344701 : List Nat := [1, 4, 1, 1, 5, 1, 2, 1, 1, 6]
def baseStart_344701 : Nat := 118140960795 + 344701 * 2 ^ 59
def prefixEnd_344701 : Nat := 4983230072969 + 3 ^ 40 * 344701 * 2
def baseEnd_344701 : Nat := 58999098361853696484085

theorem tailTrace_344701 : CollatzResearch.WordTrace tailWord_344701 prefixEnd_344701 58999098361853696484085 := by
  unfold tailWord_344701
  simp only [CollatzResearch.WordTrace]
  refine ⟨12572278324214622089009957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8381518882809748059339971 12572278324214622089009957)
  ·
    refine ⟨2357302185790241641689367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12572278324214622089009957 2357302185790241641689367)
    ·
      refine ⟨3535953278685362462534051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2357302185790241641689367 3535953278685362462534051)
      ·
        refine ⟨5303929918028043693801077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3535953278685362462534051 5303929918028043693801077)
        ·
          refine ⟨497243429815129096293851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5303929918028043693801077 497243429815129096293851)
          ·
            refine ⟨745865144722693644440777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497243429815129096293851 745865144722693644440777)
            ·
              refine ⟨559398858542020233330583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 745865144722693644440777 559398858542020233330583)
              ·
                refine ⟨839098287813030349995875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559398858542020233330583 839098287813030349995875)
                ·
                  refine ⟨1258647431719545524993813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839098287813030349995875 1258647431719545524993813)
                  ·
                    refine ⟨58999098361853696484085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1258647431719545524993813 58999098361853696484085)
                    ·
                      rfl

theorem cell23_344701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_344701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344701 prefixEnd_344701 := by exact prefixLift 344701
  have htrace : WordTrace (prefixWord ++ tailWord_344701) baseStart_344701 baseEnd_344701 := by
    simpa [prefixWord, tailWord_344701, baseEnd_344701] using wordTrace_append hprefix tailTrace_344701
  have hstable : (prefixWord ++ tailWord_344701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344701).length < 2 ^ (prefixWord ++ tailWord_344701).sum := by decide
  have hdescent : baseEnd_344701 < baseStart_344701 := by decide
  rcases family_descends (prefixWord ++ tailWord_344701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344704 : List Nat := [2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 4]
def baseStart_344704 : Nat := 118140960795 + 344704 * 2 ^ 59
def prefixEnd_344704 : Nat := 4983230072969 + 3 ^ 40 * 344704 * 2
def baseEnd_344704 : Nat := 176998835527524577714741

theorem tailTrace_344704 : CollatzResearch.WordTrace tailWord_344704 prefixEnd_344704 176998835527524577714741 := by
  unfold tailWord_344704
  simp only [CollatzResearch.WordTrace]
  refine ⟨6286193871601876800684583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8381591828802502400912777 6286193871601876800684583)
  ·
    refine ⟨9429290807402815201026875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6286193871601876800684583 9429290807402815201026875)
    ·
      refine ⟨14143936211104222801540313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9429290807402815201026875 14143936211104222801540313)
      ·
        refine ⟨10607952158328167101155235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14143936211104222801540313 10607952158328167101155235)
        ·
          refine ⟨15911928237492250651732853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10607952158328167101155235 15911928237492250651732853)
          ·
            refine ⟨1491743272264898498599955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15911928237492250651732853 1491743272264898498599955)
            ·
              refine ⟨2237614908397347747899933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491743272264898498599955 2237614908397347747899933)
              ·
                refine ⟨839105590649005405462475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2237614908397347747899933 839105590649005405462475)
                ·
                  refine ⟨1258658385973508108193713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839105590649005405462475 1258658385973508108193713)
                  ·
                    refine ⟨943993789480131081145285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1258658385973508108193713 943993789480131081145285)
                    ·
                      refine ⟨176998835527524577714741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 943993789480131081145285 176998835527524577714741)
                      ·
                        rfl

theorem cell23_344704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_344704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344704 prefixEnd_344704 := by exact prefixLift 344704
  have htrace : WordTrace (prefixWord ++ tailWord_344704) baseStart_344704 baseEnd_344704 := by
    simpa [prefixWord, tailWord_344704, baseEnd_344704] using wordTrace_append hprefix tailTrace_344704
  have hstable : (prefixWord ++ tailWord_344704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344704).length < 2 ^ (prefixWord ++ tailWord_344704).sum := by decide
  have hdescent : baseEnd_344704 < baseStart_344704 := by decide
  rcases family_descends (prefixWord ++ tailWord_344704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344708 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 5, 2, 2]
def baseStart_344708 : Nat := 118140960795 + 344708 * 2 ^ 59
def prefixEnd_344708 : Nat := 4983230072969 + 3 ^ 40 * 344708 * 2
def baseEnd_344708 : Nat := 177000889450142562064723

theorem tailTrace_344708 : CollatzResearch.WordTrace tailWord_344708 prefixEnd_344708 177000889450142562064723 := by
  unfold tailWord_344708
  simp only [CollatzResearch.WordTrace]
  refine ⟨6286266817594631142257389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8381689090126174856343185 6286266817594631142257389)
  ·
    refine ⟨2357350056597986678346521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6286266817594631142257389 2357350056597986678346521)
    ·
      refine ⟨1768012542448490008759891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2357350056597986678346521 1768012542448490008759891)
      ·
        refine ⟨2652018813672735013139837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1768012542448490008759891 2652018813672735013139837)
        ·
          refine ⟨994507055127275629927439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2652018813672735013139837 994507055127275629927439)
          ·
            refine ⟨1491760582690913444891159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994507055127275629927439 1491760582690913444891159)
            ·
              refine ⟨2237640874036370167336739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491760582690913444891159 2237640874036370167336739)
              ·
                refine ⟨3356461311054555251005109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237640874036370167336739 3356461311054555251005109)
                ·
                  refine ⟨314668247911364554781729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3356461311054555251005109 314668247911364554781729)
                  ·
                    refine ⟨236001185933523416086297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 314668247911364554781729 236001185933523416086297)
                    ·
                      refine ⟨177000889450142562064723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 236001185933523416086297 177000889450142562064723)
                      ·
                        rfl

theorem cell23_344708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 5, 2, 2].length) (baseStart_344708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344708 prefixEnd_344708 := by exact prefixLift 344708
  have htrace : WordTrace (prefixWord ++ tailWord_344708) baseStart_344708 baseEnd_344708 := by
    simpa [prefixWord, tailWord_344708, baseEnd_344708] using wordTrace_append hprefix tailTrace_344708
  have hstable : (prefixWord ++ tailWord_344708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344708).length < 2 ^ (prefixWord ++ tailWord_344708).sum := by decide
  have hdescent : baseEnd_344708 < baseStart_344708 := by decide
  rcases family_descends (prefixWord ++ tailWord_344708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344711 : List Nat := [1, 1, 4, 2, 1, 2, 2, 4, 1, 2, 3]
def baseStart_344711 : Nat := 118140960795 + 344711 * 2 ^ 59
def prefixEnd_344711 : Nat := 4983230072969 + 3 ^ 40 * 344711 * 2
def baseEnd_344711 : Nat := 177002429892106050327209

theorem tailTrace_344711 : CollatzResearch.WordTrace tailWord_344711 prefixEnd_344711 177002429892106050327209 := by
  unfold tailWord_344711
  simp only [CollatzResearch.WordTrace]
  refine ⟨12572643054178393796873987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8381762036118929197915991 12572643054178393796873987)
  ·
    refine ⟨18858964581267590695310981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12572643054178393796873987 18858964581267590695310981)
    ·
      refine ⟨3536055858987673255370809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18858964581267590695310981 3536055858987673255370809)
      ·
        refine ⟨2652041894240754941528107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3536055858987673255370809 2652041894240754941528107)
        ·
          refine ⟨3978062841361132412292161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2652041894240754941528107 3978062841361132412292161)
          ·
            refine ⟨2983547131020849309219121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3978062841361132412292161 2983547131020849309219121)
            ·
              refine ⟨2237660348265636981914341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2983547131020849309219121 2237660348265636981914341)
              ·
                refine ⟨419561315299806934108939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2237660348265636981914341 419561315299806934108939)
                ·
                  refine ⟨629341972949710401163409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419561315299806934108939 629341972949710401163409)
                  ·
                    refine ⟨472006479712282800872557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 629341972949710401163409 472006479712282800872557)
                    ·
                      refine ⟨177002429892106050327209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 472006479712282800872557 177002429892106050327209)
                      ·
                        rfl

theorem cell23_344711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_344711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344711 prefixEnd_344711 := by exact prefixLift 344711
  have htrace : WordTrace (prefixWord ++ tailWord_344711) baseStart_344711 baseEnd_344711 := by
    simpa [prefixWord, tailWord_344711, baseEnd_344711] using wordTrace_append hprefix tailTrace_344711
  have hstable : (prefixWord ++ tailWord_344711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344711).length < 2 ^ (prefixWord ++ tailWord_344711).sum := by decide
  have hdescent : baseEnd_344711 < baseStart_344711 := by decide
  rcases family_descends (prefixWord ++ tailWord_344711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344768 : List Nat := [2, 1, 1, 2, 4, 2, 1, 4, 1, 3, 2]
def baseStart_344768 : Nat := 118140960795 + 344768 * 2 ^ 59
def prefixEnd_344768 : Nat := 4983230072969 + 3 ^ 40 * 344768 * 2
def baseEnd_344768 : Nat := 177031698289412327314447

theorem tailTrace_344768 : CollatzResearch.WordTrace tailWord_344768 prefixEnd_344768 177031698289412327314447 := by
  unfold tailWord_344768
  simp only [CollatzResearch.WordTrace]
  refine ⟨6287361007485946265849479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8383148009981261687799305 6287361007485946265849479)
  ·
    refine ⟨9431041511228919398774219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6287361007485946265849479 9431041511228919398774219)
    ·
      refine ⟨14146562266843379098161329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9431041511228919398774219 14146562266843379098161329)
      ·
        refine ⟨10609921700132534323620997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14146562266843379098161329 10609921700132534323620997)
        ·
          refine ⟨1989360318774850185678937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10609921700132534323620997 1989360318774850185678937)
          ·
            refine ⟨1492020239081137639259203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1989360318774850185678937 1492020239081137639259203)
            ·
              refine ⟨2238030358621706458888805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1492020239081137639259203 2238030358621706458888805)
              ·
                refine ⟨419630692241569961041651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2238030358621706458888805 419630692241569961041651)
                ·
                  refine ⟨629446038362354941562477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419630692241569961041651 629446038362354941562477)
                  ·
                    refine ⟨236042264385883103085929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 629446038362354941562477 236042264385883103085929)
                    ·
                      refine ⟨177031698289412327314447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 236042264385883103085929 177031698289412327314447)
                      ·
                        rfl

theorem cell23_344768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4, 1, 3, 2].length) (baseStart_344768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344768 prefixEnd_344768 := by exact prefixLift 344768
  have htrace : WordTrace (prefixWord ++ tailWord_344768) baseStart_344768 baseEnd_344768 := by
    simpa [prefixWord, tailWord_344768, baseEnd_344768] using wordTrace_append hprefix tailTrace_344768
  have hstable : (prefixWord ++ tailWord_344768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344768).length < 2 ^ (prefixWord ++ tailWord_344768).sum := by decide
  have hdescent : baseEnd_344768 < baseStart_344768 := by decide
  rcases family_descends (prefixWord ++ tailWord_344768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344815 : List Nat := [1, 1, 2, 1, 5, 3, 1, 3, 2, 2, 2]
def baseStart_344815 : Nat := 118140960795 + 344815 * 2 ^ 59
def prefixEnd_344815 : Nat := 4983230072969 + 3 ^ 40 * 344815 * 2
def baseEnd_344815 : Nat := 177055831880173643426731

theorem tailTrace_344815 : CollatzResearch.WordTrace tailWord_344815 prefixEnd_344815 177055831880173643426731 := by
  unfold tailWord_344815
  simp only [CollatzResearch.WordTrace]
  refine ⟨12576436245801619558659899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8384290830534413039106599 12576436245801619558659899)
  ·
    refine ⟨18864654368702429337989849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12576436245801619558659899 18864654368702429337989849)
    ·
      refine ⟨14148490776526822003492387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18864654368702429337989849 14148490776526822003492387)
      ·
        refine ⟨21222736164790233005238581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14148490776526822003492387 21222736164790233005238581)
        ·
          refine ⟨1989631515449084344241117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21222736164790233005238581 1989631515449084344241117)
          ·
            refine ⟨746111818293406629090419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1989631515449084344241117 746111818293406629090419)
            ·
              refine ⟨1119167727440109943635629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746111818293406629090419 1119167727440109943635629)
              ·
                refine ⟨419687897790041228863361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1119167727440109943635629 419687897790041228863361)
                ·
                  refine ⟨314765923342530921647521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 419687897790041228863361 314765923342530921647521)
                  ·
                    refine ⟨236074442506898191235641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 314765923342530921647521 236074442506898191235641)
                    ·
                      refine ⟨177055831880173643426731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 236074442506898191235641 177055831880173643426731)
                      ·
                        rfl

theorem cell23_344815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 2, 2].length) (baseStart_344815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344815 prefixEnd_344815 := by exact prefixLift 344815
  have htrace : WordTrace (prefixWord ++ tailWord_344815) baseStart_344815 baseEnd_344815 := by
    simpa [prefixWord, tailWord_344815, baseEnd_344815] using wordTrace_append hprefix tailTrace_344815
  have hstable : (prefixWord ++ tailWord_344815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344815).length < 2 ^ (prefixWord ++ tailWord_344815).sum := by decide
  have hdescent : baseEnd_344815 < baseStart_344815 := by decide
  rcases family_descends (prefixWord ++ tailWord_344815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344928 : List Nat := [2, 1, 1, 3, 3, 1, 5, 1, 6]
def baseStart_344928 : Nat := 118140960795 + 344928 * 2 ^ 59
def prefixEnd_344928 : Nat := 4983230072969 + 3 ^ 40 * 344928 * 2
def baseEnd_344928 : Nat := 19679317243792411257079

theorem tailTrace_344928 : CollatzResearch.WordTrace tailWord_344928 prefixEnd_344928 19679317243792411257079 := by
  unfold tailWord_344928
  simp only [CollatzResearch.WordTrace]
  refine ⟨6290278847196119928761719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8387038462928159905015625 6290278847196119928761719)
  ·
    refine ⟨9435418270794179893142579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6290278847196119928761719 9435418270794179893142579)
    ·
      refine ⟨14153127406191269839713869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9435418270794179893142579 14153127406191269839713869)
      ·
        refine ⟨5307422777321726189892701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14153127406191269839713869 5307422777321726189892701)
        ·
          refine ⟨1990283541495647321209763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5307422777321726189892701 1990283541495647321209763)
          ·
            refine ⟨2985425312243470981814645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990283541495647321209763 2985425312243470981814645)
            ·
              refine ⟨279883623022825404545123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2985425312243470981814645 279883623022825404545123)
              ·
                refine ⟨419825434534238106817685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 279883623022825404545123 419825434534238106817685)
                ·
                  refine ⟨19679317243792411257079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 419825434534238106817685 19679317243792411257079)
                  ·
                    rfl

theorem cell23_344928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 6].length) (baseStart_344928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344928 prefixEnd_344928 := by exact prefixLift 344928
  have htrace : WordTrace (prefixWord ++ tailWord_344928) baseStart_344928 baseEnd_344928 := by
    simpa [prefixWord, tailWord_344928, baseEnd_344928] using wordTrace_append hprefix tailTrace_344928
  have hstable : (prefixWord ++ tailWord_344928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344928).length < 2 ^ (prefixWord ++ tailWord_344928).sum := by decide
  have hdescent : baseEnd_344928 < baseStart_344928 := by decide
  rcases family_descends (prefixWord ++ tailWord_344928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344965 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 2, 3, 2]
def baseStart_344965 : Nat := 118140960795 + 344965 * 2 ^ 59
def prefixEnd_344965 : Nat := 4983230072969 + 3 ^ 40 * 344965 * 2
def baseEnd_344965 : Nat := 177132853978348056551041

theorem tailTrace_344965 : CollatzResearch.WordTrace tailWord_344965 prefixEnd_344965 177132853978348056551041 := by
  unfold tailWord_344965
  simp only [CollatzResearch.WordTrace]
  refine ⟨12581907195258195176620349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8387938130172130117746899 12581907195258195176620349)
  ·
    refine ⟨4718215198221823191232631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12581907195258195176620349 4718215198221823191232631)
    ·
      refine ⟨7077322797332734786848947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4718215198221823191232631 7077322797332734786848947)
      ·
        refine ⟨10615984195999102180273421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7077322797332734786848947 10615984195999102180273421)
        ·
          refine ⟨3980994073499663317602533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10615984195999102180273421 3980994073499663317602533)
          ·
            refine ⟨746436388781186872050475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3980994073499663317602533 746436388781186872050475)
            ·
              refine ⟨1119654583171780308075713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746436388781186872050475 1119654583171780308075713)
              ·
                refine ⟨839740937378835231056785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1119654583171780308075713 839740937378835231056785)
                ·
                  refine ⟨629805703034126423292589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 839740937378835231056785 629805703034126423292589)
                  ·
                    refine ⟨236177138637797408734721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 629805703034126423292589 236177138637797408734721)
                    ·
                      refine ⟨177132853978348056551041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 236177138637797408734721 177132853978348056551041)
                      ·
                        rfl

theorem cell23_344965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 3, 2].length) (baseStart_344965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344965 prefixEnd_344965 := by exact prefixLift 344965
  have htrace : WordTrace (prefixWord ++ tailWord_344965) baseStart_344965 baseEnd_344965 := by
    simpa [prefixWord, tailWord_344965, baseEnd_344965] using wordTrace_append hprefix tailTrace_344965
  have hstable : (prefixWord ++ tailWord_344965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344965).length < 2 ^ (prefixWord ++ tailWord_344965).sum := by decide
  have hdescent : baseEnd_344965 < baseStart_344965 := by decide
  rcases family_descends (prefixWord ++ tailWord_344965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344995 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 3, 2, 2]
def baseStart_344995 : Nat := 118140960795 + 344995 * 2 ^ 59
def prefixEnd_344995 : Nat := 4983230072969 + 3 ^ 40 * 344995 * 2
def baseEnd_344995 : Nat := 177148258397982939175903

theorem tailTrace_344995 : CollatzResearch.WordTrace tailWord_344995 prefixEnd_344995 177148258397982939175903 := by
  unfold tailWord_344995
  simp only [CollatzResearch.WordTrace]
  refine ⟨12583001385149510300212439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8388667590099673533474959 12583001385149510300212439)
  ·
    refine ⟨18874502077724265450318659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12583001385149510300212439 18874502077724265450318659)
    ·
      refine ⟨28311753116586398175477989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18874502077724265450318659 28311753116586398175477989)
      ·
        refine ⟨5308453709359949657902123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28311753116586398175477989 5308453709359949657902123)
        ·
          refine ⟨7962680564039924486853185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5308453709359949657902123 7962680564039924486853185)
          ·
            refine ⟨5972010423029943365139889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7962680564039924486853185 5972010423029943365139889)
            ·
              refine ⟨4479007817272457523854917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5972010423029943365139889 4479007817272457523854917)
              ·
                refine ⟨839813965738585785722797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4479007817272457523854917 839813965738585785722797)
                ·
                  refine ⟨314930237151969669646049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 839813965738585785722797 314930237151969669646049)
                  ·
                    refine ⟨236197677863977252234537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 314930237151969669646049 236197677863977252234537)
                    ·
                      refine ⟨177148258397982939175903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 236197677863977252234537 177148258397982939175903)
                      ·
                        rfl

theorem cell23_344995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 2, 2].length) (baseStart_344995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_344995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_344995 prefixEnd_344995 := by exact prefixLift 344995
  have htrace : WordTrace (prefixWord ++ tailWord_344995) baseStart_344995 baseEnd_344995 := by
    simpa [prefixWord, tailWord_344995, baseEnd_344995] using wordTrace_append hprefix tailTrace_344995
  have hstable : (prefixWord ++ tailWord_344995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344995).length < 2 ^ (prefixWord ++ tailWord_344995).sum := by decide
  have hdescent : baseEnd_344995 < baseStart_344995 := by decide
  rcases family_descends (prefixWord ++ tailWord_344995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345031 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 2, 7]
def baseStart_345031 : Nat := 118140960795 + 345031 * 2 ^ 59
def prefixEnd_345031 : Nat := 4983230072969 + 3 ^ 40 * 345031 * 2
def baseEnd_345031 : Nat := 59055581233848266108579

theorem tailTrace_345031 : CollatzResearch.WordTrace tailWord_345031 prefixEnd_345031 59055581233848266108579 := by
  unfold tailWord_345031
  simp only [CollatzResearch.WordTrace]
  refine ⟨12584314413019088448522947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8389542942012725632348631 12584314413019088448522947)
  ·
    refine ⟨18876471619528632672784421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12584314413019088448522947 18876471619528632672784421)
    ·
      refine ⟨3539338428661618626147079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18876471619528632672784421 3539338428661618626147079)
      ·
        refine ⟨5309007642992427939220619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3539338428661618626147079 5309007642992427939220619)
        ·
          refine ⟨7963511464488641908830929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5309007642992427939220619 7963511464488641908830929)
          ·
            refine ⟨5972633598366481431623197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7963511464488641908830929 5972633598366481431623197)
            ·
              refine ⟨2239737599387430536858699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5972633598366481431623197 2239737599387430536858699)
              ·
                refine ⟨3359606399081145805288049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2239737599387430536858699 3359606399081145805288049)
                ·
                  refine ⟨2519704799310859353966037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3359606399081145805288049 2519704799310859353966037)
                  ·
                    refine ⟨59055581233848266108579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2519704799310859353966037 59055581233848266108579)
                    ·
                      rfl

theorem cell23_345031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_345031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345031 prefixEnd_345031 := by exact prefixLift 345031
  have htrace : WordTrace (prefixWord ++ tailWord_345031) baseStart_345031 baseEnd_345031 := by
    simpa [prefixWord, tailWord_345031, baseEnd_345031] using wordTrace_append hprefix tailTrace_345031
  have hstable : (prefixWord ++ tailWord_345031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345031).length < 2 ^ (prefixWord ++ tailWord_345031).sum := by decide
  have hdescent : baseEnd_345031 < baseStart_345031 := by decide
  rcases family_descends (prefixWord ++ tailWord_345031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345102 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2]
def baseStart_345102 : Nat := 118140960795 + 345102 * 2 ^ 59
def prefixEnd_345102 : Nat := 4983230072969 + 3 ^ 40 * 345102 * 2
def baseEnd_345102 : Nat := 177203200828014020537911

theorem tailTrace_345102 : CollatzResearch.WordTrace tailWord_345102 prefixEnd_345102 177203200828014020537911 := by
  unfold tailWord_345102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1573362999470233446794695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8391269330507911716238373 1573362999470233446794695)
  ·
    refine ⟨2360044499205350170192043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1573362999470233446794695 2360044499205350170192043)
    ·
      refine ⟨3540066748808025255288065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2360044499205350170192043 3540066748808025255288065)
      ·
        refine ⟨2655050061606018941466049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3540066748808025255288065 2655050061606018941466049)
        ·
          refine ⟨1991287546204514206099537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2655050061606018941466049 1991287546204514206099537)
          ·
            refine ⟨1493465659653385654574653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1991287546204514206099537 1493465659653385654574653)
            ·
              refine ⟨560049622370019620465495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1493465659653385654574653 560049622370019620465495)
              ·
                refine ⟨840074433555029430698243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560049622370019620465495 840074433555029430698243)
                ·
                  refine ⟨1260111650332544146047365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840074433555029430698243 1260111650332544146047365)
                  ·
                    refine ⟨236270934437352027383881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1260111650332544146047365 236270934437352027383881)
                    ·
                      refine ⟨177203200828014020537911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 236270934437352027383881 177203200828014020537911)
                      ·
                        rfl

theorem cell23_345102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_345102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345102 prefixEnd_345102 := by exact prefixLift 345102
  have htrace : WordTrace (prefixWord ++ tailWord_345102) baseStart_345102 baseEnd_345102 := by
    simpa [prefixWord, tailWord_345102, baseEnd_345102] using wordTrace_append hprefix tailTrace_345102
  have hstable : (prefixWord ++ tailWord_345102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345102).length < 2 ^ (prefixWord ++ tailWord_345102).sum := by decide
  have hdescent : baseEnd_345102 < baseStart_345102 := by decide
  rcases family_descends (prefixWord ++ tailWord_345102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345142 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 7]
def baseStart_345142 : Nat := 118140960795 + 345142 * 2 ^ 59
def prefixEnd_345142 : Nat := 4983230072969 + 3 ^ 40 * 345142 * 2
def baseEnd_345142 : Nat := 19691526672688207115303

theorem tailTrace_345142 : CollatzResearch.WordTrace tailWord_345142 prefixEnd_345142 19691526672688207115303 := by
  unfold tailWord_345142
  simp only [CollatzResearch.WordTrace]
  refine ⟨786772682226059650363355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8392241943744636270542453 786772682226059650363355)
  ·
    refine ⟨1180159023339089475545033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 786772682226059650363355 1180159023339089475545033)
    ·
      refine ⟨885119267504317106658775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1180159023339089475545033 885119267504317106658775)
      ·
        refine ⟨1327678901256475659988163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 885119267504317106658775 1327678901256475659988163)
        ·
          refine ⟨1991518351884713489982245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1327678901256475659988163 1991518351884713489982245)
          ·
            refine ⟨373409690978383779371671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1991518351884713489982245 373409690978383779371671)
            ·
              refine ⟨560114536467575669057507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373409690978383779371671 560114536467575669057507)
              ·
                refine ⟨840171804701363503586261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560114536467575669057507 840171804701363503586261)
                ·
                  refine ⟨19691526672688207115303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 840171804701363503586261 19691526672688207115303)
                  ·
                    rfl

theorem cell23_345142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_345142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345142 prefixEnd_345142 := by exact prefixLift 345142
  have htrace : WordTrace (prefixWord ++ tailWord_345142) baseStart_345142 baseEnd_345142 := by
    simpa [prefixWord, tailWord_345142, baseEnd_345142] using wordTrace_append hprefix tailTrace_345142
  have hstable : (prefixWord ++ tailWord_345142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345142).length < 2 ^ (prefixWord ++ tailWord_345142).sum := by decide
  have hdescent : baseEnd_345142 < baseStart_345142 := by decide
  rcases family_descends (prefixWord ++ tailWord_345142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345148 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 7]
def baseStart_345148 : Nat := 118140960795 + 345148 * 2 ^ 59
def prefixEnd_345148 : Nat := 4983230072969 + 3 ^ 40 * 345148 * 2
def baseEnd_345148 : Nat := 177226820938120840562699

theorem tailTrace_345148 : CollatzResearch.WordTrace tailWord_345148 prefixEnd_345148 177226820938120840562699 := by
  unfold tailWord_345148
  simp only [CollatzResearch.WordTrace]
  refine ⟨6294290876797608715266049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8392387835730144953688065 6294290876797608715266049)
  ·
    refine ⟨4720718157598206536449537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6294290876797608715266049 4720718157598206536449537)
    ·
      refine ⟨3540538618198654902337153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4720718157598206536449537 3540538618198654902337153)
      ·
        refine ⟨2655403963648991176752865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3540538618198654902337153 2655403963648991176752865)
        ·
          refine ⟨1991552972736743382564649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2655403963648991176752865 1991552972736743382564649)
          ·
            refine ⟨1493664729552557536923487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1991552972736743382564649 1493664729552557536923487)
            ·
              refine ⟨2240497094328836305385231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1493664729552557536923487 2240497094328836305385231)
              ·
                refine ⟨3360745641493254458077847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2240497094328836305385231 3360745641493254458077847)
                ·
                  refine ⟨5041118462239881687116771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3360745641493254458077847 5041118462239881687116771)
                  ·
                    refine ⟨7561677693359822530675157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5041118462239881687116771 7561677693359822530675157)
                    ·
                      refine ⟨177226820938120840562699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7561677693359822530675157 177226820938120840562699)
                      ·
                        rfl

theorem cell23_345148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_345148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345148 prefixEnd_345148 := by exact prefixLift 345148
  have htrace : WordTrace (prefixWord ++ tailWord_345148) baseStart_345148 baseEnd_345148 := by
    simpa [prefixWord, tailWord_345148, baseEnd_345148] using wordTrace_append hprefix tailTrace_345148
  have hstable : (prefixWord ++ tailWord_345148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345148).length < 2 ^ (prefixWord ++ tailWord_345148).sum := by decide
  have hdescent : baseEnd_345148 < baseStart_345148 := by decide
  rcases family_descends (prefixWord ++ tailWord_345148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345153 : List Nat := [1, 2, 5, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_345153 : Nat := 118140960795 + 345153 * 2 ^ 59
def prefixEnd_345153 : Nat := 4983230072969 + 3 ^ 40 * 345153 * 2
def baseEnd_345153 : Nat := 177229388341393321000177

theorem tailTrace_345153 : CollatzResearch.WordTrace tailWord_345153 prefixEnd_345153 177229388341393321000177 := by
  unfold tailWord_345153
  simp only [CollatzResearch.WordTrace]
  refine ⟨12588764118577103284464113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8392509412384735522976075 12588764118577103284464113)
  ·
    refine ⟨9441573088932827463348085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12588764118577103284464113 9441573088932827463348085)
    ·
      refine ⟨885147477087452574688883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9441573088932827463348085 885147477087452574688883)
      ·
        refine ⟨1327721215631178862033325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 885147477087452574688883 1327721215631178862033325)
        ·
          refine ⟨497895455861692073262497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1327721215631178862033325 497895455861692073262497)
          ·
            refine ⟨373421591896269054946873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 497895455861692073262497 373421591896269054946873)
            ·
              refine ⟨280066193922201791210155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373421591896269054946873 280066193922201791210155)
              ·
                refine ⟨420099290883302686815233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280066193922201791210155 420099290883302686815233)
                ·
                  refine ⟨315074468162477015111425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420099290883302686815233 315074468162477015111425)
                  ·
                    refine ⟨236305851121857761333569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 315074468162477015111425 236305851121857761333569)
                    ·
                      refine ⟨177229388341393321000177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 236305851121857761333569 177229388341393321000177)
                      ·
                        rfl

theorem cell23_345153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_345153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345153 prefixEnd_345153 := by exact prefixLift 345153
  have htrace : WordTrace (prefixWord ++ tailWord_345153) baseStart_345153 baseEnd_345153 := by
    simpa [prefixWord, tailWord_345153, baseEnd_345153] using wordTrace_append hprefix tailTrace_345153
  have hstable : (prefixWord ++ tailWord_345153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345153).length < 2 ^ (prefixWord ++ tailWord_345153).sum := by decide
  have hdescent : baseEnd_345153 < baseStart_345153 := by decide
  rcases family_descends (prefixWord ++ tailWord_345153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345175 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 4, 4, 2]
def baseStart_345175 : Nat := 118140960795 + 345175 * 2 ^ 59
def prefixEnd_345175 : Nat := 4983230072969 + 3 ^ 40 * 345175 * 2
def baseEnd_345175 : Nat := 177240684915792234925075

theorem tailTrace_345175 : CollatzResearch.WordTrace tailWord_345175 prefixEnd_345175 177240684915792234925075 := by
  unfold tailWord_345175
  simp only [CollatzResearch.WordTrace]
  refine ⟨12589566524497401041764979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8393044349664934027843319 12589566524497401041764979)
  ·
    refine ⟨18884349786746101562647469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12589566524497401041764979 18884349786746101562647469)
    ·
      refine ⟨7081631170029788085992801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18884349786746101562647469 7081631170029788085992801)
      ·
        refine ⟨5311223377522341064494601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7081631170029788085992801 5311223377522341064494601)
        ·
          refine ⟨3983417533141755798370951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5311223377522341064494601 3983417533141755798370951)
          ·
            refine ⟨5975126299712633697556427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983417533141755798370951 5975126299712633697556427)
            ·
              refine ⟨8962689449568950546334641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5975126299712633697556427 8962689449568950546334641)
              ·
                refine ⟨6722017087176712909750981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8962689449568950546334641 6722017087176712909750981)
                ·
                  refine ⟨1260378203845633670578309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6722017087176712909750981 1260378203845633670578309)
                  ·
                    refine ⟨236320913221056313233433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1260378203845633670578309 236320913221056313233433)
                    ·
                      refine ⟨177240684915792234925075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 236320913221056313233433 177240684915792234925075)
                      ·
                        rfl

theorem cell23_345175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 4, 2].length) (baseStart_345175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345175 prefixEnd_345175 := by exact prefixLift 345175
  have htrace : WordTrace (prefixWord ++ tailWord_345175) baseStart_345175 baseEnd_345175 := by
    simpa [prefixWord, tailWord_345175, baseEnd_345175] using wordTrace_append hprefix tailTrace_345175
  have hstable : (prefixWord ++ tailWord_345175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345175).length < 2 ^ (prefixWord ++ tailWord_345175).sum := by decide
  have hdescent : baseEnd_345175 < baseStart_345175 := by decide
  rcases family_descends (prefixWord ++ tailWord_345175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345188 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 2, 1, 6]
def baseStart_345188 : Nat := 118140960795 + 345188 * 2 ^ 59
def prefixEnd_345188 : Nat := 4983230072969 + 3 ^ 40 * 345188 * 2
def baseEnd_345188 : Nat := 177247360164300684062515

theorem tailTrace_345188 : CollatzResearch.WordTrace tailWord_345188 prefixEnd_345188 177247360164300684062515 := by
  unfold tailWord_345188
  simp only [CollatzResearch.WordTrace]
  refine ⟨6295020336725152130994109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8393360448966869507992145 6295020336725152130994109)
  ·
    refine ⟨2360632626271932049122791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6295020336725152130994109 2360632626271932049122791)
    ·
      refine ⟨3540948939407898073684187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2360632626271932049122791 3540948939407898073684187)
      ·
        refine ⟨5311423409111847110526281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3540948939407898073684187 5311423409111847110526281)
        ·
          refine ⟨3983567556833885332894711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5311423409111847110526281 3983567556833885332894711)
          ·
            refine ⟨5975351335250827999342067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983567556833885332894711 5975351335250827999342067)
            ·
              refine ⟨8963027002876241999013101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5975351335250827999342067 8963027002876241999013101)
              ·
                refine ⟨3361135126078590749629913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8963027002876241999013101 3361135126078590749629913)
                ·
                  refine ⟨2520851344558943062222435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3361135126078590749629913 2520851344558943062222435)
                  ·
                    refine ⟨3781277016838414593333653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2520851344558943062222435 3781277016838414593333653)
                    ·
                      refine ⟨177247360164300684062515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3781277016838414593333653 177247360164300684062515)
                      ·
                        rfl

theorem cell23_345188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_345188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345188 prefixEnd_345188 := by exact prefixLift 345188
  have htrace : WordTrace (prefixWord ++ tailWord_345188) baseStart_345188 baseEnd_345188 := by
    simpa [prefixWord, tailWord_345188, baseEnd_345188] using wordTrace_append hprefix tailTrace_345188
  have hstable : (prefixWord ++ tailWord_345188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345188).length < 2 ^ (prefixWord ++ tailWord_345188).sum := by decide
  have hdescent : baseEnd_345188 < baseStart_345188 := by decide
  rcases family_descends (prefixWord ++ tailWord_345188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345316 : List Nat := [2, 3, 1, 1, 1, 2, 2, 6, 1, 2, 2]
def baseStart_345316 : Nat := 118140960795 + 345316 * 2 ^ 59
def prefixEnd_345316 : Nat := 4983230072969 + 3 ^ 40 * 345316 * 2
def baseEnd_345316 : Nat := 177313085688076183261927

theorem tailTrace_345316 : CollatzResearch.WordTrace tailWord_345316 prefixEnd_345316 177313085688076183261927 := by
  unfold tailWord_345316
  simp only [CollatzResearch.WordTrace]
  refine ⟨6297354608493291061323901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8396472811324388081765201 6297354608493291061323901)
  ·
    refine ⟨2361507978184984147996463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6297354608493291061323901 2361507978184984147996463)
    ·
      refine ⟨3542261967277476221994695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2361507978184984147996463 3542261967277476221994695)
      ·
        refine ⟨5313392950916214332992043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3542261967277476221994695 5313392950916214332992043)
        ·
          refine ⟨7970089426374321499488065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5313392950916214332992043 7970089426374321499488065)
          ·
            refine ⟨5977567069780741124616049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7970089426374321499488065 5977567069780741124616049)
            ·
              refine ⟨4483175302335555843462037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5977567069780741124616049 4483175302335555843462037)
              ·
                refine ⟨210148842296979180162283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4483175302335555843462037 210148842296979180162283)
                ·
                  refine ⟨315223263445468770243425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210148842296979180162283 315223263445468770243425)
                  ·
                    refine ⟨236417447584101577682569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 315223263445468770243425 236417447584101577682569)
                    ·
                      refine ⟨177313085688076183261927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 236417447584101577682569 177313085688076183261927)
                      ·
                        rfl

theorem cell23_345316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_345316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345316 prefixEnd_345316 := by exact prefixLift 345316
  have htrace : WordTrace (prefixWord ++ tailWord_345316) baseStart_345316 baseEnd_345316 := by
    simpa [prefixWord, tailWord_345316, baseEnd_345316] using wordTrace_append hprefix tailTrace_345316
  have hstable : (prefixWord ++ tailWord_345316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345316).length < 2 ^ (prefixWord ++ tailWord_345316).sum := by decide
  have hdescent : baseEnd_345316 < baseStart_345316 := by decide
  rcases family_descends (prefixWord ++ tailWord_345316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345365 : List Nat := [1, 3, 2, 1, 2, 1, 1, 4, 2, 6]
def baseStart_345365 : Nat := 118140960795 + 345365 * 2 ^ 59
def prefixEnd_345365 : Nat := 4983230072969 + 3 ^ 40 * 345365 * 2
def baseEnd_345365 : Nat := 59112748746715497183067

theorem tailTrace_345365 : CollatzResearch.WordTrace tailWord_345365 prefixEnd_345365 59112748746715497183067 := by
  unfold tailWord_345365
  simp only [CollatzResearch.WordTrace]
  refine ⟨12596496393809063491181549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8397664262539375660787699 12596496393809063491181549)
  ·
    refine ⟨4723686147678398809193081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12596496393809063491181549 4723686147678398809193081)
    ·
      refine ⟨3542764610758799106894811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4723686147678398809193081 3542764610758799106894811)
      ·
        refine ⟨5314146916138198660342217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3542764610758799106894811 5314146916138198660342217)
        ·
          refine ⟨3985610187103648995256663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5314146916138198660342217 3985610187103648995256663)
          ·
            refine ⟨5978415280655473492884995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3985610187103648995256663 5978415280655473492884995)
            ·
              refine ⟨8967622920983210239327493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5978415280655473492884995 8967622920983210239327493)
              ·
                refine ⟨1681429297684351919873905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8967622920983210239327493 1681429297684351919873905)
                ·
                  refine ⟨1261071973263263939905429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1681429297684351919873905 1261071973263263939905429)
                  ·
                    refine ⟨59112748746715497183067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1261071973263263939905429 59112748746715497183067)
                    ·
                      rfl

theorem cell23_345365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 6].length) (baseStart_345365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345365 prefixEnd_345365 := by exact prefixLift 345365
  have htrace : WordTrace (prefixWord ++ tailWord_345365) baseStart_345365 baseEnd_345365 := by
    simpa [prefixWord, tailWord_345365, baseEnd_345365] using wordTrace_append hprefix tailTrace_345365
  have hstable : (prefixWord ++ tailWord_345365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345365).length < 2 ^ (prefixWord ++ tailWord_345365).sum := by decide
  have hdescent : baseEnd_345365 < baseStart_345365 := by decide
  rcases family_descends (prefixWord ++ tailWord_345365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345395 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 9]
def baseStart_345395 : Nat := 118140960795 + 345395 * 2 ^ 59
def prefixEnd_345395 : Nat := 4983230072969 + 3 ^ 40 * 345395 * 2
def baseEnd_345395 : Nat := 19705961184420152686007

theorem tailTrace_345395 : CollatzResearch.WordTrace tailWord_345395 prefixEnd_345395 19705961184420152686007 := by
  unfold tailWord_345395
  simp only [CollatzResearch.WordTrace]
  refine ⟨12597590583700378614773639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8398393722466919076515759 12597590583700378614773639)
  ·
    refine ⟨18896385875550567922160459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12597590583700378614773639 18896385875550567922160459)
    ·
      refine ⟨28344578813325851883240689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18896385875550567922160459 28344578813325851883240689)
      ·
        refine ⟨21258434109994388912430517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28344578813325851883240689 21258434109994388912430517)
        ·
          refine ⟨1992978197811973960540361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21258434109994388912430517 1992978197811973960540361)
          ·
            refine ⟨1494733648358980470405271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1992978197811973960540361 1494733648358980470405271)
            ·
              refine ⟨2242100472538470705607907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494733648358980470405271 2242100472538470705607907)
              ·
                refine ⟨3363150708807706058411861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2242100472538470705607907 3363150708807706058411861)
                ·
                  refine ⟨19705961184420152686007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3363150708807706058411861 19705961184420152686007)
                  ·
                    rfl

theorem cell23_345395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 9].length) (baseStart_345395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345395 prefixEnd_345395 := by exact prefixLift 345395
  have htrace : WordTrace (prefixWord ++ tailWord_345395) baseStart_345395 baseEnd_345395 := by
    simpa [prefixWord, tailWord_345395, baseEnd_345395] using wordTrace_append hprefix tailTrace_345395
  have hstable : (prefixWord ++ tailWord_345395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345395).length < 2 ^ (prefixWord ++ tailWord_345395).sum := by decide
  have hdescent : baseEnd_345395 < baseStart_345395 := by decide
  rcases family_descends (prefixWord ++ tailWord_345395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345406 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 4, 2, 2]
def baseStart_345406 : Nat := 118140960795 + 345406 * 2 ^ 59
def prefixEnd_345406 : Nat := 4983230072969 + 3 ^ 40 * 345406 * 2
def baseEnd_345406 : Nat := 177359298946980831136513

theorem tailTrace_345406 : CollatzResearch.WordTrace tailWord_345406 prefixEnd_345406 177359298946980831136513 := by
  unfold tailWord_345406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1574748973332565936678009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8398661191107018328949381 1574748973332565936678009)
  ·
    refine ⟨1181061729999424452508507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1574748973332565936678009 1181061729999424452508507)
    ·
      refine ⟨1771592594999136678762761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1181061729999424452508507 1771592594999136678762761)
      ·
        refine ⟨1328694446249352509072071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1771592594999136678762761 1328694446249352509072071)
        ·
          refine ⟨1993041669374028763608107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328694446249352509072071 1993041669374028763608107)
          ·
            refine ⟨2989562504061043145412161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993041669374028763608107 2989562504061043145412161)
            ·
              refine ⟨2242171878045782359059121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2989562504061043145412161 2242171878045782359059121)
              ·
                refine ⟨1681628908534336769294341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2242171878045782359059121 1681628908534336769294341)
                ·
                  refine ⟨315305420350188144242689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1681628908534336769294341 315305420350188144242689)
                  ·
                    refine ⟨236479065262641108182017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 315305420350188144242689 236479065262641108182017)
                    ·
                      refine ⟨177359298946980831136513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 236479065262641108182017 177359298946980831136513)
                      ·
                        rfl

theorem cell23_345406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_345406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345406 prefixEnd_345406 := by exact prefixLift 345406
  have htrace : WordTrace (prefixWord ++ tailWord_345406) baseStart_345406 baseEnd_345406 := by
    simpa [prefixWord, tailWord_345406, baseEnd_345406] using wordTrace_append hprefix tailTrace_345406
  have hstable : (prefixWord ++ tailWord_345406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345406).length < 2 ^ (prefixWord ++ tailWord_345406).sum := by decide
  have hdescent : baseEnd_345406 < baseStart_345406 := by decide
  rcases family_descends (prefixWord ++ tailWord_345406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345422 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3]
def baseStart_345422 : Nat := 118140960795 + 345422 * 2 ^ 59
def prefixEnd_345422 : Nat := 4983230072969 + 3 ^ 40 * 345422 * 2
def baseEnd_345422 : Nat := 177367514637452768536439

theorem tailTrace_345422 : CollatzResearch.WordTrace tailWord_345422 prefixEnd_345422 177367514637452768536439 := by
  unfold tailWord_345422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1574821919325320278250815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8399050236401708150671013 1574821919325320278250815)
  ·
    refine ⟨2362232878987980417376223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1574821919325320278250815 2362232878987980417376223)
    ·
      refine ⟨3543349318481970626064335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2362232878987980417376223 3543349318481970626064335)
      ·
        refine ⟨5315023977722955939096503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3543349318481970626064335 5315023977722955939096503)
        ·
          refine ⟨7972535966584433908644755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5315023977722955939096503 7972535966584433908644755)
          ·
            refine ⟨11958803949876650862967133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7972535966584433908644755 11958803949876650862967133)
            ·
              refine ⟨4484551481203744073612675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11958803949876650862967133 4484551481203744073612675)
              ·
                refine ⟨6726827221805616110419013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4484551481203744073612675 6726827221805616110419013)
                ·
                  refine ⟨1261280104088553020703565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6726827221805616110419013 1261280104088553020703565)
                  ·
                    refine ⟨472980039033207382763837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1261280104088553020703565 472980039033207382763837)
                    ·
                      refine ⟨177367514637452768536439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 472980039033207382763837 177367514637452768536439)
                      ·
                        rfl

theorem cell23_345422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 4, 3, 3].length) (baseStart_345422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345422 prefixEnd_345422 := by exact prefixLift 345422
  have htrace : WordTrace (prefixWord ++ tailWord_345422) baseStart_345422 baseEnd_345422 := by
    simpa [prefixWord, tailWord_345422, baseEnd_345422] using wordTrace_append hprefix tailTrace_345422
  have hstable : (prefixWord ++ tailWord_345422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345422).length < 2 ^ (prefixWord ++ tailWord_345422).sum := by decide
  have hdescent : baseEnd_345422 < baseStart_345422 := by decide
  rcases family_descends (prefixWord ++ tailWord_345422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345429 : List Nat := [1, 3, 2, 2, 3, 1, 2, 4, 5]
def baseStart_345429 : Nat := 118140960795 + 345429 * 2 ^ 59
def prefixEnd_345429 : Nat := 4983230072969 + 3 ^ 40 * 345429 * 2
def baseEnd_345429 : Nat := 19707901000226026794323

theorem tailTrace_345429 : CollatzResearch.WordTrace tailWord_345429 prefixEnd_345429 19707901000226026794323 := by
  unfold tailWord_345429
  simp only [CollatzResearch.WordTrace]
  refine ⟨12598830665577202421511341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8399220443718134947674227 12598830665577202421511341)
  ·
    refine ⟨4724561499591450908066753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12598830665577202421511341 4724561499591450908066753)
    ·
      refine ⟨3543421124693588181050065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4724561499591450908066753 3543421124693588181050065)
      ·
        refine ⟨2657565843520191135787549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3543421124693588181050065 2657565843520191135787549)
        ·
          refine ⟨996587191320071675920331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2657565843520191135787549 996587191320071675920331)
          ·
            refine ⟨1494880786980107513880497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996587191320071675920331 1494880786980107513880497)
            ·
              refine ⟨1121160590235080635410373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1494880786980107513880497 1121160590235080635410373)
              ·
                refine ⟨210217610669077619139445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1121160590235080635410373 210217610669077619139445)
                ·
                  refine ⟨19707901000226026794323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 210217610669077619139445 19707901000226026794323)
                  ·
                    rfl

theorem cell23_345429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 5].length) (baseStart_345429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345429 prefixEnd_345429 := by exact prefixLift 345429
  have htrace : WordTrace (prefixWord ++ tailWord_345429) baseStart_345429 baseEnd_345429 := by
    simpa [prefixWord, tailWord_345429, baseEnd_345429] using wordTrace_append hprefix tailTrace_345429
  have hstable : (prefixWord ++ tailWord_345429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345429).length < 2 ^ (prefixWord ++ tailWord_345429).sum := by decide
  have hdescent : baseEnd_345429 < baseStart_345429 := by decide
  rcases family_descends (prefixWord ++ tailWord_345429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345442 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_345442 : Nat := 118140960795 + 345442 * 2 ^ 59
def prefixEnd_345442 : Nat := 4983230072969 + 3 ^ 40 * 345442 * 2
def baseEnd_345442 : Nat := 59125928083514230095449

theorem tailTrace_345442 : CollatzResearch.WordTrace tailWord_345442 prefixEnd_345442 59125928083514230095449 := by
  unfold tailWord_345442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3149826203632526410433645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8399536543020070427823053 3149826203632526410433645)
  ·
    refine ⟨1181184826362197403912617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3149826203632526410433645 1181184826362197403912617)
    ·
      refine ⟨885888619771648052934463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1181184826362197403912617 885888619771648052934463)
      ·
        refine ⟨1328832929657472079401695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 885888619771648052934463 1328832929657472079401695)
        ·
          refine ⟨1993249394486208119102543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328832929657472079401695 1993249394486208119102543)
          ·
            refine ⟨2989874091729312178653815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993249394486208119102543 2989874091729312178653815)
            ·
              refine ⟨4484811137593968267980723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989874091729312178653815 4484811137593968267980723)
              ·
                refine ⟨6727216706390952401971085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4484811137593968267980723 6727216706390952401971085)
                ·
                  refine ⟨2522706264896607150739157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6727216706390952401971085 2522706264896607150739157)
                  ·
                    refine ⟨59125928083514230095449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2522706264896607150739157 59125928083514230095449)
                    ·
                      rfl

theorem cell23_345442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_345442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345442 prefixEnd_345442 := by exact prefixLift 345442
  have htrace : WordTrace (prefixWord ++ tailWord_345442) baseStart_345442 baseEnd_345442 := by
    simpa [prefixWord, tailWord_345442, baseEnd_345442] using wordTrace_append hprefix tailTrace_345442
  have hstable : (prefixWord ++ tailWord_345442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345442).length < 2 ^ (prefixWord ++ tailWord_345442).sum := by decide
  have hdescent : baseEnd_345442 < baseStart_345442 := by decide
  rcases family_descends (prefixWord ++ tailWord_345442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345455 : List Nat := [1, 1, 2, 1, 3, 1, 3, 1, 2, 8]
def baseStart_345455 : Nat := 118140960795 + 345455 * 2 ^ 59
def prefixEnd_345455 : Nat := 4983230072969 + 3 ^ 40 * 345455 * 2
def baseEnd_345455 : Nat := 59128153166350379807929

theorem tailTrace_345455 : CollatzResearch.WordTrace tailWord_345455 prefixEnd_345455 59128153166350379807929 := by
  unfold tailWord_345455
  simp only [CollatzResearch.WordTrace]
  refine ⟨12599778963483008861957819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8399852642322005907971879 12599778963483008861957819)
  ·
    refine ⟨18899668445224513292936729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12599778963483008861957819 18899668445224513292936729)
    ·
      refine ⟨14174751333918384969702547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18899668445224513292936729 14174751333918384969702547)
      ·
        refine ⟨21262127000877577454553821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14174751333918384969702547 21262127000877577454553821)
        ·
          refine ⟨7973297625329091545457683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21262127000877577454553821 7973297625329091545457683)
          ·
            refine ⟨11959946437993637318186525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7973297625329091545457683 11959946437993637318186525)
            ·
              refine ⟨4484979914247613994319947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11959946437993637318186525 4484979914247613994319947)
              ·
                refine ⟨6727469871371420991479921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4484979914247613994319947 6727469871371420991479921)
                ·
                  refine ⟨5045602403528565743609941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6727469871371420991479921 5045602403528565743609941)
                  ·
                    refine ⟨59128153166350379807929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5045602403528565743609941 59128153166350379807929)
                    ·
                      rfl

theorem cell23_345455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 8].length) (baseStart_345455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345455 prefixEnd_345455 := by exact prefixLift 345455
  have htrace : WordTrace (prefixWord ++ tailWord_345455) baseStart_345455 baseEnd_345455 := by
    simpa [prefixWord, tailWord_345455, baseEnd_345455] using wordTrace_append hprefix tailTrace_345455
  have hstable : (prefixWord ++ tailWord_345455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345455).length < 2 ^ (prefixWord ++ tailWord_345455).sum := by decide
  have hdescent : baseEnd_345455 < baseStart_345455 := by decide
  rcases family_descends (prefixWord ++ tailWord_345455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345472 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 5, 4]
def baseStart_345472 : Nat := 118140960795 + 345472 * 2 ^ 59
def prefixEnd_345472 : Nat := 4983230072969 + 3 ^ 40 * 345472 * 2
def baseEnd_345472 : Nat := 59131062890059190970403

theorem tailTrace_345472 : CollatzResearch.WordTrace tailWord_345472 prefixEnd_345472 59131062890059190970403 := by
  unfold tailWord_345472
  simp only [CollatzResearch.WordTrace]
  refine ⟨6300199502210710382663335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8400266002947613843551113 6300199502210710382663335)
  ·
    refine ⟨9450299253316065573995003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6300199502210710382663335 9450299253316065573995003)
    ·
      refine ⟨14175448879974098360992505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9450299253316065573995003 14175448879974098360992505)
      ·
        refine ⟨10631586659980573770744379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14175448879974098360992505 10631586659980573770744379)
        ·
          refine ⟨15947379989970860656116569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10631586659980573770744379 15947379989970860656116569)
          ·
            refine ⟨11960534992478145492087427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15947379989970860656116569 11960534992478145492087427)
            ·
              refine ⟨17940802488717218238131141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11960534992478145492087427 17940802488717218238131141)
              ·
                refine ⟨3363900466634478419649589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17940802488717218238131141 3363900466634478419649589)
                ·
                  refine ⟨315365668746982351842149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3363900466634478419649589 315365668746982351842149)
                  ·
                    refine ⟨59131062890059190970403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 315365668746982351842149 59131062890059190970403)
                    ·
                      rfl

theorem cell23_345472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 5, 4].length) (baseStart_345472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345472 prefixEnd_345472 := by exact prefixLift 345472
  have htrace : WordTrace (prefixWord ++ tailWord_345472) baseStart_345472 baseEnd_345472 := by
    simpa [prefixWord, tailWord_345472, baseEnd_345472] using wordTrace_append hprefix tailTrace_345472
  have hstable : (prefixWord ++ tailWord_345472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345472).length < 2 ^ (prefixWord ++ tailWord_345472).sum := by decide
  have hdescent : baseEnd_345472 < baseStart_345472 := by decide
  rcases family_descends (prefixWord ++ tailWord_345472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345479 : List Nat := [1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 4]
def baseStart_345479 : Nat := 118140960795 + 345479 * 2 ^ 59
def prefixEnd_345479 : Nat := 4983230072969 + 3 ^ 40 * 345479 * 2
def baseEnd_345479 : Nat := 177396783034759045523677

theorem tailTrace_345479 : CollatzResearch.WordTrace tailWord_345479 prefixEnd_345479 177396783034759045523677 := by
  unfold tailWord_345479
  simp only [CollatzResearch.WordTrace]
  refine ⟨12600654315396060960831491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8400436210264040640554327 12600654315396060960831491)
  ·
    refine ⟨18900981473094091441247237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12600654315396060960831491 18900981473094091441247237)
    ·
      refine ⟨3543934026205142145233857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18900981473094091441247237 3543934026205142145233857)
      ·
        refine ⟨2657950519653856608925393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3543934026205142145233857 2657950519653856608925393)
        ·
          refine ⟨1993462889740392456694045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2657950519653856608925393 1993462889740392456694045)
          ·
            refine ⟨747548583652647171260267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1993462889740392456694045 747548583652647171260267)
            ·
              refine ⟨1121322875478970756890401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747548583652647171260267 1121322875478970756890401)
              ·
                refine ⟨840992156609228067667801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1121322875478970756890401 840992156609228067667801)
                ·
                  refine ⟨630744117456921050750851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 840992156609228067667801 630744117456921050750851)
                  ·
                    refine ⟨946116176185381576126277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 630744117456921050750851 946116176185381576126277)
                    ·
                      refine ⟨177396783034759045523677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 946116176185381576126277 177396783034759045523677)
                      ·
                        rfl

theorem cell23_345479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_345479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345479 prefixEnd_345479 := by exact prefixLift 345479
  have htrace : WordTrace (prefixWord ++ tailWord_345479) baseStart_345479 baseEnd_345479 := by
    simpa [prefixWord, tailWord_345479, baseEnd_345479] using wordTrace_append hprefix tailTrace_345479
  have hstable : (prefixWord ++ tailWord_345479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345479).length < 2 ^ (prefixWord ++ tailWord_345479).sum := by decide
  have hdescent : baseEnd_345479 < baseStart_345479 := by decide
  rcases family_descends (prefixWord ++ tailWord_345479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345540 : List Nat := [2, 3, 3, 2, 1, 1, 4, 2, 1, 4]
def baseStart_345540 : Nat := 118140960795 + 345540 * 2 ^ 59
def prefixEnd_345540 : Nat := 4983230072969 + 3 ^ 40 * 345540 * 2
def baseEnd_345540 : Nat := 59142701784894435620299

theorem tailTrace_345540 : CollatzResearch.WordTrace tailWord_345540 prefixEnd_345540 59142701784894435620299 := by
  unfold tailWord_345540
  simp only [CollatzResearch.WordTrace]
  refine ⟨6301439584087534189401037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8401919445450045585868049 6301439584087534189401037)
  ·
    refine ⟨2363039844032825321025389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6301439584087534189401037 2363039844032825321025389)
    ·
      refine ⟨886139941512309495384521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2363039844032825321025389 886139941512309495384521)
      ·
        refine ⟨664604956134232121538391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 886139941512309495384521 664604956134232121538391)
        ·
          refine ⟨996907434201348182307587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 664604956134232121538391 996907434201348182307587)
          ·
            refine ⟨1495361151302022273461381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996907434201348182307587 1495361151302022273461381)
            ·
              refine ⟨280380215869129176274009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1495361151302022273461381 280380215869129176274009)
              ·
                refine ⟨210285161901846882205507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280380215869129176274009 210285161901846882205507)
                ·
                  refine ⟨315427742852770323308261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210285161901846882205507 315427742852770323308261)
                  ·
                    refine ⟨59142701784894435620299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 315427742852770323308261 59142701784894435620299)
                    ·
                      rfl

theorem cell23_345540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_345540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345540 prefixEnd_345540 := by exact prefixLift 345540
  have htrace : WordTrace (prefixWord ++ tailWord_345540) baseStart_345540 baseEnd_345540 := by
    simpa [prefixWord, tailWord_345540, baseEnd_345540] using wordTrace_append hprefix tailTrace_345540
  have hstable : (prefixWord ++ tailWord_345540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345540).length < 2 ^ (prefixWord ++ tailWord_345540).sum := by decide
  have hdescent : baseEnd_345540 < baseStart_345540 := by decide
  rcases family_descends (prefixWord ++ tailWord_345540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345569 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_345569 : Nat := 118140960795 + 345569 * 2 ^ 59
def prefixEnd_345569 : Nat := 4983230072969 + 3 ^ 40 * 345569 * 2
def baseEnd_345569 : Nat := 177442996293663693398263

theorem tailTrace_345569 : CollatzResearch.WordTrace tailWord_345569 prefixEnd_345569 177442996293663693398263 := by
  unfold tailWord_345569
  simp only [CollatzResearch.WordTrace]
  refine ⟨12603936885070006331607761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8402624590046670887738507 12603936885070006331607761)
  ·
    refine ⟨9452952663802504748705821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12603936885070006331607761 9452952663802504748705821)
    ·
      refine ⟨3544857248925939280764683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9452952663802504748705821 3544857248925939280764683)
      ·
        refine ⟨5317285873388908921147025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3544857248925939280764683 5317285873388908921147025)
        ·
          refine ⟨3987964405041681690860269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5317285873388908921147025 3987964405041681690860269)
          ·
            refine ⟨1495486651890630634072601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3987964405041681690860269 1495486651890630634072601)
            ·
              refine ⟨1121614988917972975554451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1495486651890630634072601 1121614988917972975554451)
              ·
                refine ⟨1682422483376959463331677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121614988917972975554451 1682422483376959463331677)
                ·
                  refine ⟨630908431266359798749379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1682422483376959463331677 630908431266359798749379)
                  ·
                    refine ⟨946362646899539698124069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 630908431266359798749379 946362646899539698124069)
                    ·
                      refine ⟨177442996293663693398263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 946362646899539698124069 177442996293663693398263)
                      ·
                        rfl

theorem cell23_345569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_345569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345569 prefixEnd_345569 := by exact prefixLift 345569
  have htrace : WordTrace (prefixWord ++ tailWord_345569) baseStart_345569 baseEnd_345569 := by
    simpa [prefixWord, tailWord_345569, baseEnd_345569] using wordTrace_append hprefix tailTrace_345569
  have hstable : (prefixWord ++ tailWord_345569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345569).length < 2 ^ (prefixWord ++ tailWord_345569).sum := by decide
  have hdescent : baseEnd_345569 < baseStart_345569 := by decide
  rcases family_descends (prefixWord ++ tailWord_345569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345573 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 2, 3, 2]
def baseStart_345573 : Nat := 118140960795 + 345573 * 2 ^ 59
def prefixEnd_345573 : Nat := 4983230072969 + 3 ^ 40 * 345573 * 2
def baseEnd_345573 : Nat := 177445050216281677748245

theorem tailTrace_345573 : CollatzResearch.WordTrace tailWord_345573 prefixEnd_345573 177445050216281677748245 := by
  unfold tailWord_345573
  simp only [CollatzResearch.WordTrace]
  refine ⟨12604082777055515014753373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8402721851370343343168915 12604082777055515014753373)
  ·
    refine ⟨4726531041395818130532515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12604082777055515014753373 4726531041395818130532515)
    ·
      refine ⟨7089796562093727195798773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4726531041395818130532515 7089796562093727195798773)
      ·
        refine ⟨664668427696286924606135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7089796562093727195798773 664668427696286924606135)
        ·
          refine ⟨997002641544430386909203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 664668427696286924606135 997002641544430386909203)
          ·
            refine ⟨1495503962316645580363805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997002641544430386909203 1495503962316645580363805)
            ·
              refine ⟨560813985868742092636427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1495503962316645580363805 560813985868742092636427)
              ·
                refine ⟨841220978803113138954641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560813985868742092636427 841220978803113138954641)
                ·
                  refine ⟨630915734102334854215981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 841220978803113138954641 630915734102334854215981)
                  ·
                    refine ⟨236593400288375570330993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 630915734102334854215981 236593400288375570330993)
                    ·
                      refine ⟨177445050216281677748245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 236593400288375570330993 177445050216281677748245)
                      ·
                        rfl

theorem cell23_345573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_345573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345573 prefixEnd_345573 := by exact prefixLift 345573
  have htrace : WordTrace (prefixWord ++ tailWord_345573) baseStart_345573 baseEnd_345573 := by
    simpa [prefixWord, tailWord_345573, baseEnd_345573] using wordTrace_append hprefix tailTrace_345573
  have hstable : (prefixWord ++ tailWord_345573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345573).length < 2 ^ (prefixWord ++ tailWord_345573).sum := by decide
  have hdescent : baseEnd_345573 < baseStart_345573 := by decide
  rcases family_descends (prefixWord ++ tailWord_345573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345592 : List Nat := [2, 1, 2, 1, 1, 6, 10]
def baseStart_345592 : Nat := 118140960795 + 345592 * 2 ^ 59
def prefixEnd_345592 : Nat := 4983230072969 + 3 ^ 40 * 345592 * 2
def baseEnd_345592 : Nat := 2190800078379223498897

theorem tailTrace_345592 : CollatzResearch.WordTrace tailWord_345592 prefixEnd_345592 2190800078379223498897 := by
  unfold tailWord_345592
  simp only [CollatzResearch.WordTrace]
  refine ⟨6302387881993340629847515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8403183842657787506463353 6302387881993340629847515)
  ·
    refine ⟨9453581822990010944771273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6302387881993340629847515 9453581822990010944771273)
    ·
      refine ⟨7090186367242508208578455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9453581822990010944771273 7090186367242508208578455)
      ·
        refine ⟨10635279550863762312867683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7090186367242508208578455 10635279550863762312867683)
        ·
          refine ⟨15952919326295643469301525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10635279550863762312867683 15952919326295643469301525)
          ·
            refine ⟨747793093420108287623509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15952919326295643469301525 747793093420108287623509)
            ·
              refine ⟨2190800078379223498897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 747793093420108287623509 2190800078379223498897)
              ·
                rfl

theorem cell23_345592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 10].length) (baseStart_345592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345592 prefixEnd_345592 := by exact prefixLift 345592
  have htrace : WordTrace (prefixWord ++ tailWord_345592) baseStart_345592 baseEnd_345592 := by
    simpa [prefixWord, tailWord_345592, baseEnd_345592] using wordTrace_append hprefix tailTrace_345592
  have hstable : (prefixWord ++ tailWord_345592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345592).length < 2 ^ (prefixWord ++ tailWord_345592).sum := by decide
  have hdescent : baseEnd_345592 < baseStart_345592 := by decide
  rcases family_descends (prefixWord ++ tailWord_345592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345596 : List Nat := [2, 2, 2, 1, 2, 1, 5, 2, 2, 4]
def baseStart_345596 : Nat := 118140960795 + 345596 * 2 ^ 59
def prefixEnd_345596 : Nat := 4983230072969 + 3 ^ 40 * 345596 * 2
def baseEnd_345596 : Nat := 59152286757111695920213

theorem tailTrace_345596 : CollatzResearch.WordTrace tailWord_345596 prefixEnd_345596 59152286757111695920213 := by
  unfold tailWord_345596
  simp only [CollatzResearch.WordTrace]
  refine ⟨6302460827986094971420321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8403281103981459961893761 6302460827986094971420321)
  ·
    refine ⟨4726845620989571228565241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6302460827986094971420321 4726845620989571228565241)
    ·
      refine ⟨3545134215742178421423931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4726845620989571228565241 3545134215742178421423931)
      ·
        refine ⟨5317701323613267632135897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3545134215742178421423931 5317701323613267632135897)
        ·
          refine ⟨3988275992709950724101923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5317701323613267632135897 3988275992709950724101923)
          ·
            refine ⟨5982413989064926086152885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3988275992709950724101923 5982413989064926086152885)
            ·
              refine ⟨560851311474836820576833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5982413989064926086152885 560851311474836820576833)
              ·
                refine ⟨420638483606127615432625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560851311474836820576833 420638483606127615432625)
                ·
                  refine ⟨315478862704595711574469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 420638483606127615432625 315478862704595711574469)
                  ·
                    refine ⟨59152286757111695920213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 315478862704595711574469 59152286757111695920213)
                    ·
                      rfl

theorem cell23_345596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_345596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345596 prefixEnd_345596 := by exact prefixLift 345596
  have htrace : WordTrace (prefixWord ++ tailWord_345596) baseStart_345596 baseEnd_345596 := by
    simpa [prefixWord, tailWord_345596, baseEnd_345596] using wordTrace_append hprefix tailTrace_345596
  have hstable : (prefixWord ++ tailWord_345596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345596).length < 2 ^ (prefixWord ++ tailWord_345596).sum := by decide
  have hdescent : baseEnd_345596 < baseStart_345596 := by decide
  rcases family_descends (prefixWord ++ tailWord_345596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345620 : List Nat := [2, 4, 3, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_345620 : Nat := 118140960795 + 345620 * 2 ^ 59
def prefixEnd_345620 : Nat := 4983230072969 + 3 ^ 40 * 345620 * 2
def baseEnd_345620 : Nat := 177469183807042993860529

theorem tailTrace_345620 : CollatzResearch.WordTrace tailWord_345620 prefixEnd_345620 177469183807042993860529 := by
  unfold tailWord_345620
  simp only [CollatzResearch.WordTrace]
  refine ⟨6302898503942621020857157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8403864671923494694476209 6302898503942621020857157)
  ·
    refine ⟨1181793469489241441410717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6302898503942621020857157 1181793469489241441410717)
    ·
      refine ⟨443172551058465540529019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1181793469489241441410717 443172551058465540529019)
      ·
        refine ⟨664758826587698310793529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443172551058465540529019 664758826587698310793529)
        ·
          refine ⟨498569119940773733095147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 664758826587698310793529 498569119940773733095147)
          ·
            refine ⟨747853679911160599642721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498569119940773733095147 747853679911160599642721)
            ·
              refine ⟨560890259933370449732041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 747853679911160599642721 560890259933370449732041)
              ·
                refine ⟨420667694950027837299031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560890259933370449732041 420667694950027837299031)
                ·
                  refine ⟨631001542425041755948547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420667694950027837299031 631001542425041755948547)
                  ·
                    refine ⟨946502313637562633922821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 631001542425041755948547 946502313637562633922821)
                    ·
                      refine ⟨177469183807042993860529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 946502313637562633922821 177469183807042993860529)
                      ·
                        rfl

theorem cell23_345620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_345620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345620 prefixEnd_345620 := by exact prefixLift 345620
  have htrace : WordTrace (prefixWord ++ tailWord_345620) baseStart_345620 baseEnd_345620 := by
    simpa [prefixWord, tailWord_345620, baseEnd_345620] using wordTrace_append hprefix tailTrace_345620
  have hstable : (prefixWord ++ tailWord_345620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345620).length < 2 ^ (prefixWord ++ tailWord_345620).sum := by decide
  have hdescent : baseEnd_345620 < baseStart_345620 := by decide
  rcases family_descends (prefixWord ++ tailWord_345620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345654 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 3, 2, 2]
def baseStart_345654 : Nat := 118140960795 + 345654 * 2 ^ 59
def prefixEnd_345654 : Nat := 4983230072969 + 3 ^ 40 * 345654 * 2
def baseEnd_345654 : Nat := 177486642149295860835373

theorem tailTrace_345654 : CollatzResearch.WordTrace tailWord_345654 prefixEnd_345654 177486642149295860835373 := by
  unfold tailWord_345654
  simp only [CollatzResearch.WordTrace]
  refine ⟨787939818110129115528251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8404691393174710565634677 787939818110129115528251)
  ·
    refine ⟨1181909727165193673292377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 787939818110129115528251 1181909727165193673292377)
    ·
      refine ⟨886432295373895254969283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1181909727165193673292377 886432295373895254969283)
      ·
        refine ⟨1329648443060842882453925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886432295373895254969283 1329648443060842882453925)
        ·
          refine ⟨249309083073908040460111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1329648443060842882453925 249309083073908040460111)
          ·
            refine ⟨373963624610862060690167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249309083073908040460111 373963624610862060690167)
            ·
              refine ⟨560945436916293091035251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373963624610862060690167 560945436916293091035251)
              ·
                refine ⟨841418155374439636552877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560945436916293091035251 841418155374439636552877)
                ·
                  refine ⟨315531808265414863707329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841418155374439636552877 315531808265414863707329)
                  ·
                    refine ⟨236648856199061147780497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 315531808265414863707329 236648856199061147780497)
                    ·
                      refine ⟨177486642149295860835373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 236648856199061147780497 177486642149295860835373)
                      ·
                        rfl

theorem cell23_345654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 3, 2, 2].length) (baseStart_345654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345654 prefixEnd_345654 := by exact prefixLift 345654
  have htrace : WordTrace (prefixWord ++ tailWord_345654) baseStart_345654 baseEnd_345654 := by
    simpa [prefixWord, tailWord_345654, baseEnd_345654] using wordTrace_append hprefix tailTrace_345654
  have hstable : (prefixWord ++ tailWord_345654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345654).length < 2 ^ (prefixWord ++ tailWord_345654).sum := by decide
  have hdescent : baseEnd_345654 < baseStart_345654 := by decide
  rcases family_descends (prefixWord ++ tailWord_345654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345776 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 3, 4]
def baseStart_345776 : Nat := 118140960795 + 345776 * 2 ^ 59
def prefixEnd_345776 : Nat := 4983230072969 + 3 ^ 40 * 345776 * 2
def baseEnd_345776 : Nat := 59183095596381461169937

theorem tailTrace_345776 : CollatzResearch.WordTrace tailWord_345776 prefixEnd_345776 59183095596381461169937 := by
  unfold tailWord_345776
  simp only [CollatzResearch.WordTrace]
  refine ⟨6305743397660040342196591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8407657863546720456262121 6305743397660040342196591)
  ·
    refine ⟨9458615096490060513294887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6305743397660040342196591 9458615096490060513294887)
    ·
      refine ⟨14187922644735090769942331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9458615096490060513294887 14187922644735090769942331)
      ·
        refine ⟨21281883967102636154913497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14187922644735090769942331 21281883967102636154913497)
        ·
          refine ⟨15961412975326977116185123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21281883967102636154913497 15961412975326977116185123)
          ·
            refine ⟨23942119462990465674277685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15961412975326977116185123 23942119462990465674277685)
            ·
              refine ⟨2244573699655356156963533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23942119462990465674277685 2244573699655356156963533)
              ·
                refine ⟨841715137370758558861325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2244573699655356156963533 841715137370758558861325)
                ·
                  refine ⟨315643176514034459572997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841715137370758558861325 315643176514034459572997)
                  ·
                    refine ⟨59183095596381461169937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 315643176514034459572997 59183095596381461169937)
                    ·
                      rfl

theorem cell23_345776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 3, 4].length) (baseStart_345776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345776 prefixEnd_345776 := by exact prefixLift 345776
  have htrace : WordTrace (prefixWord ++ tailWord_345776) baseStart_345776 baseEnd_345776 := by
    simpa [prefixWord, tailWord_345776, baseEnd_345776] using wordTrace_append hprefix tailTrace_345776
  have hstable : (prefixWord ++ tailWord_345776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345776).length < 2 ^ (prefixWord ++ tailWord_345776).sum := by decide
  have hdescent : baseEnd_345776 < baseStart_345776 := by decide
  rcases family_descends (prefixWord ++ tailWord_345776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345779 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 6]
def baseStart_345779 : Nat := 118140960795 + 345779 * 2 ^ 59
def prefixEnd_345779 : Nat := 4983230072969 + 3 ^ 40 * 345779 * 2
def baseEnd_345779 : Nat := 177550827231107871772297

theorem tailTrace_345779 : CollatzResearch.WordTrace tailWord_345779 prefixEnd_345779 177550827231107871772297 := by
  unfold tailWord_345779
  simp only [CollatzResearch.WordTrace]
  refine ⟨12611596214309212196752391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8407730809539474797834927 12611596214309212196752391)
  ·
    refine ⟨18917394321463818295128587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12611596214309212196752391 18917394321463818295128587)
    ·
      refine ⟨28376091482195727442692881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18917394321463818295128587 28376091482195727442692881)
      ·
        refine ⟨21282068611646795582019661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28376091482195727442692881 21282068611646795582019661)
        ·
          refine ⟨7980775729367548343257373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21282068611646795582019661 7980775729367548343257373)
          ·
            refine ⟨2992790898512830628721515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7980775729367548343257373 2992790898512830628721515)
            ·
              refine ⟨4489186347769245943082273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2992790898512830628721515 4489186347769245943082273)
              ·
                refine ⟨3366889760826934457311705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4489186347769245943082273 3366889760826934457311705)
                ·
                  refine ⟨2525167320620200842983779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3366889760826934457311705 2525167320620200842983779)
                  ·
                    refine ⟨3787750980930301264475669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2525167320620200842983779 3787750980930301264475669)
                    ·
                      refine ⟨177550827231107871772297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3787750980930301264475669 177550827231107871772297)
                      ·
                        rfl

theorem cell23_345779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_345779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345779 prefixEnd_345779 := by exact prefixLift 345779
  have htrace : WordTrace (prefixWord ++ tailWord_345779) baseStart_345779 baseEnd_345779 := by
    simpa [prefixWord, tailWord_345779, baseEnd_345779] using wordTrace_append hprefix tailTrace_345779
  have hstable : (prefixWord ++ tailWord_345779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345779).length < 2 ^ (prefixWord ++ tailWord_345779).sum := by decide
  have hdescent : baseEnd_345779 < baseStart_345779 := by decide
  rcases family_descends (prefixWord ++ tailWord_345779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345783 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 2, 4, 2]
def baseStart_345783 : Nat := 118140960795 + 345783 * 2 ^ 59
def prefixEnd_345783 : Nat := 4983230072969 + 3 ^ 40 * 345783 * 2
def baseEnd_345783 : Nat := 177552881153725856122279

theorem tailTrace_345783 : CollatzResearch.WordTrace tailWord_345783 prefixEnd_345783 177552881153725856122279 := by
  unfold tailWord_345783
  simp only [CollatzResearch.WordTrace]
  refine ⟨12611742106294720879898003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8407828070863147253265335 12611742106294720879898003)
  ·
    refine ⟨18917613159442081319847005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12611742106294720879898003 18917613159442081319847005)
    ·
      refine ⟨7094104934790780494942627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18917613159442081319847005 7094104934790780494942627)
      ·
        refine ⟨10641157402186170742413941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7094104934790780494942627 10641157402186170742413941)
        ·
          refine ⟨997608506454953507101307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10641157402186170742413941 997608506454953507101307)
          ·
            refine ⟨1496412759682430260651961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997608506454953507101307 1496412759682430260651961)
            ·
              refine ⟨1122309569761822695488971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1496412759682430260651961 1122309569761822695488971)
              ·
                refine ⟨1683464354642734043233457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122309569761822695488971 1683464354642734043233457)
                ·
                  refine ⟨1262598265982050532425093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1683464354642734043233457 1262598265982050532425093)
                  ·
                    refine ⟨236737174871634474829705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1262598265982050532425093 236737174871634474829705)
                    ·
                      refine ⟨177552881153725856122279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 236737174871634474829705 177552881153725856122279)
                      ·
                        rfl

theorem cell23_345783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 4, 2].length) (baseStart_345783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345783 prefixEnd_345783 := by exact prefixLift 345783
  have htrace : WordTrace (prefixWord ++ tailWord_345783) baseStart_345783 baseEnd_345783 := by
    simpa [prefixWord, tailWord_345783, baseEnd_345783] using wordTrace_append hprefix tailTrace_345783
  have hstable : (prefixWord ++ tailWord_345783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345783).length < 2 ^ (prefixWord ++ tailWord_345783).sum := by decide
  have hdescent : baseEnd_345783 < baseStart_345783 := by decide
  rcases family_descends (prefixWord ++ tailWord_345783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345786 : List Nat := [3, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3]
def baseStart_345786 : Nat := 118140960795 + 345786 * 2 ^ 59
def prefixEnd_345786 : Nat := 4983230072969 + 3 ^ 40 * 345786 * 2
def baseEnd_345786 : Nat := 177554421595689344384765

theorem tailTrace_345786 : CollatzResearch.WordTrace tailWord_345786 prefixEnd_345786 177554421595689344384765 := by
  unfold tailWord_345786
  simp only [CollatzResearch.WordTrace]
  refine ⟨3152962881320963098064303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8407901016855901594838141 3152962881320963098064303)
  ·
    refine ⟨4729444321981444647096455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3152962881320963098064303 4729444321981444647096455)
    ·
      refine ⟨7094166482972166970644683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4729444321981444647096455 7094166482972166970644683)
      ·
        refine ⟨10641249724458250455967025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7094166482972166970644683 10641249724458250455967025)
        ·
          refine ⟨7980937293343687841975269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10641249724458250455967025 7980937293343687841975269)
          ·
            refine ⟨1496425742501941470370363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7980937293343687841975269 1496425742501941470370363)
            ·
              refine ⟨2244638613752912205555545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496425742501941470370363 2244638613752912205555545)
              ·
                refine ⟨1683478960314684154166659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2244638613752912205555545 1683478960314684154166659)
                ·
                  refine ⟨2525218440472026231249989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683478960314684154166659 2525218440472026231249989)
                  ·
                    refine ⟨473478457588504918359373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2525218440472026231249989 473478457588504918359373)
                    ·
                      refine ⟨177554421595689344384765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 473478457588504918359373 177554421595689344384765)
                      ·
                        rfl

theorem cell23_345786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_345786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345786 prefixEnd_345786 := by exact prefixLift 345786
  have htrace : WordTrace (prefixWord ++ tailWord_345786) baseStart_345786 baseEnd_345786 := by
    simpa [prefixWord, tailWord_345786, baseEnd_345786] using wordTrace_append hprefix tailTrace_345786
  have hstable : (prefixWord ++ tailWord_345786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345786).length < 2 ^ (prefixWord ++ tailWord_345786).sum := by decide
  have hdescent : baseEnd_345786 < baseStart_345786 := by decide
  rcases family_descends (prefixWord ++ tailWord_345786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345796 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_345796 : Nat := 118140960795 + 345796 * 2 ^ 59
def prefixEnd_345796 : Nat := 4983230072969 + 3 ^ 40 * 345796 * 2
def baseEnd_345796 : Nat := 177559556402234305259719

theorem tailTrace_345796 : CollatzResearch.WordTrace tailWord_345796 prefixEnd_345796 177559556402234305259719 := by
  unfold tailWord_345796
  simp only [CollatzResearch.WordTrace]
  refine ⟨6306108127623812050060621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8408144170165082733414161 6306108127623812050060621)
  ·
    refine ⟨2364790547858929518772733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6306108127623812050060621 2364790547858929518772733)
    ·
      refine ⟨886796455447098569539775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2364790547858929518772733 886796455447098569539775)
      ·
        refine ⟨1330194683170647854309663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886796455447098569539775 1330194683170647854309663)
        ·
          refine ⟨1995292024755971781464495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1330194683170647854309663 1995292024755971781464495)
          ·
            refine ⟨2992938037133957672196743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995292024755971781464495 2992938037133957672196743)
            ·
              refine ⟨4489407055700936508295115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2992938037133957672196743 4489407055700936508295115)
              ·
                refine ⟨6734110583551404762442673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4489407055700936508295115 6734110583551404762442673)
                ·
                  refine ⟨5050582937663553571832005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6734110583551404762442673 5050582937663553571832005)
                  ·
                    refine ⟨946984300811916294718501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5050582937663553571832005 946984300811916294718501)
                    ·
                      refine ⟨177559556402234305259719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 946984300811916294718501 177559556402234305259719)
                      ·
                        rfl

theorem cell23_345796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_345796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345796 prefixEnd_345796 := by exact prefixLift 345796
  have htrace : WordTrace (prefixWord ++ tailWord_345796) baseStart_345796 baseEnd_345796 := by
    simpa [prefixWord, tailWord_345796, baseEnd_345796] using wordTrace_append hprefix tailTrace_345796
  have hstable : (prefixWord ++ tailWord_345796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345796).length < 2 ^ (prefixWord ++ tailWord_345796).sum := by decide
  have hdescent : baseEnd_345796 < baseStart_345796 := by decide
  rcases family_descends (prefixWord ++ tailWord_345796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345827 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 3, 4]
def baseStart_345827 : Nat := 118140960795 + 345827 * 2 ^ 59
def prefixEnd_345827 : Nat := 4983230072969 + 3 ^ 40 * 345827 * 2
def baseEnd_345827 : Nat := 59191824767507894657359

theorem tailTrace_345827 : CollatzResearch.WordTrace tailWord_345827 prefixEnd_345827 59191824767507894657359 := by
  unfold tailWord_345827
  simp only [CollatzResearch.WordTrace]
  refine ⟨12613346918135316394499735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8408897945423544262999823 12613346918135316394499735)
  ·
    refine ⟨18920020377202974591749603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12613346918135316394499735 18920020377202974591749603)
    ·
      refine ⟨28380030565804461887624405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18920020377202974591749603 28380030565804461887624405)
      ·
        refine ⟨665156966386042075491197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 28380030565804461887624405 665156966386042075491197)
        ·
          refine ⟨249433862394765778309199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 665156966386042075491197 249433862394765778309199)
          ·
            refine ⟨374150793592148667463799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249433862394765778309199 374150793592148667463799)
            ·
              refine ⟨561226190388223001195699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374150793592148667463799 561226190388223001195699)
              ·
                refine ⟨841839285582334501793549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561226190388223001195699 841839285582334501793549)
                ·
                  refine ⟨315689732093375438172581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 841839285582334501793549 315689732093375438172581)
                  ·
                    refine ⟨59191824767507894657359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 315689732093375438172581 59191824767507894657359)
                    ·
                      rfl

theorem cell23_345827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 3, 4].length) (baseStart_345827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345827 prefixEnd_345827 := by exact prefixLift 345827
  have htrace : WordTrace (prefixWord ++ tailWord_345827) baseStart_345827 baseEnd_345827 := by
    simpa [prefixWord, tailWord_345827, baseEnd_345827] using wordTrace_append hprefix tailTrace_345827
  have hstable : (prefixWord ++ tailWord_345827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345827).length < 2 ^ (prefixWord ++ tailWord_345827).sum := by decide
  have hdescent : baseEnd_345827 < baseStart_345827 := by decide
  rcases family_descends (prefixWord ++ tailWord_345827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345856 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 4]
def baseStart_345856 : Nat := 118140960795 + 345856 * 2 ^ 59
def prefixEnd_345856 : Nat := 4983230072969 + 3 ^ 40 * 345856 * 2
def baseEnd_345856 : Nat := 177590365241504070509443

theorem tailTrace_345856 : CollatzResearch.WordTrace tailWord_345856 prefixEnd_345856 177590365241504070509443 := by
  unfold tailWord_345856
  simp only [CollatzResearch.WordTrace]
  refine ⟨6307202317515127173652711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8409603090020169564870281 6307202317515127173652711)
  ·
    refine ⟨9460803476272690760479067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6307202317515127173652711 9460803476272690760479067)
    ·
      refine ⟨14191205214409036140718601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9460803476272690760479067 14191205214409036140718601)
      ·
        refine ⟨10643403910806777105538951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14191205214409036140718601 10643403910806777105538951)
        ·
          refine ⟨15965105866210165658308427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10643403910806777105538951 15965105866210165658308427)
          ·
            refine ⟨23947658799315248487462641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15965105866210165658308427 23947658799315248487462641)
            ·
              refine ⟨17960744099486436365596981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23947658799315248487462641 17960744099486436365596981)
              ·
                refine ⟨1683819759326853409274717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17960744099486436365596981 1683819759326853409274717)
                ·
                  refine ⟨631432409747570028478019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1683819759326853409274717 631432409747570028478019)
                  ·
                    refine ⟨947148614621355042717029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 631432409747570028478019 947148614621355042717029)
                    ·
                      refine ⟨177590365241504070509443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 947148614621355042717029 177590365241504070509443)
                      ·
                        rfl

theorem cell23_345856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_345856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345856 prefixEnd_345856 := by exact prefixLift 345856
  have htrace : WordTrace (prefixWord ++ tailWord_345856) baseStart_345856 baseEnd_345856 := by
    simpa [prefixWord, tailWord_345856, baseEnd_345856] using wordTrace_append hprefix tailTrace_345856
  have hstable : (prefixWord ++ tailWord_345856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345856).length < 2 ^ (prefixWord ++ tailWord_345856).sum := by decide
  have hdescent : baseEnd_345856 < baseStart_345856 := by decide
  rcases family_descends (prefixWord ++ tailWord_345856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345860 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 2, 3, 2]
def baseStart_345860 : Nat := 118140960795 + 345860 * 2 ^ 59
def prefixEnd_345860 : Nat := 4983230072969 + 3 ^ 40 * 345860 * 2
def baseEnd_345860 : Nat := 177592419164122054859425

theorem tailTrace_345860 : CollatzResearch.WordTrace tailWord_345860 prefixEnd_345860 177592419164122054859425 := by
  unfold tailWord_345860
  simp only [CollatzResearch.WordTrace]
  refine ⟨6307275263507881515225517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8409700351343842020300689 6307275263507881515225517)
  ·
    refine ⟨2365228223815455568209569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6307275263507881515225517 2365228223815455568209569)
    ·
      refine ⟨1773921167861591676157177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2365228223815455568209569 1773921167861591676157177)
      ·
        refine ⟨1330440875896193757117883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1773921167861591676157177 1330440875896193757117883)
        ·
          refine ⟨1995661313844290635676825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1330440875896193757117883 1995661313844290635676825)
          ·
            refine ⟨1496745985383217976757619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1995661313844290635676825 1496745985383217976757619)
            ·
              refine ⟨2245118978074826965136429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496745985383217976757619 2245118978074826965136429)
              ·
                refine ⟨841919616778060111926161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2245118978074826965136429 841919616778060111926161)
                ·
                  refine ⟨631439712583545083944621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 841919616778060111926161 631439712583545083944621)
                  ·
                    refine ⟨236789892218829406479233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 631439712583545083944621 236789892218829406479233)
                    ·
                      refine ⟨177592419164122054859425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 236789892218829406479233 177592419164122054859425)
                      ·
                        rfl

theorem cell23_345860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_345860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345860 prefixEnd_345860 := by exact prefixLift 345860
  have htrace : WordTrace (prefixWord ++ tailWord_345860) baseStart_345860 baseEnd_345860 := by
    simpa [prefixWord, tailWord_345860, baseEnd_345860] using wordTrace_append hprefix tailTrace_345860
  have hstable : (prefixWord ++ tailWord_345860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345860).length < 2 ^ (prefixWord ++ tailWord_345860).sum := by decide
  have hdescent : baseEnd_345860 < baseStart_345860 := by decide
  rcases family_descends (prefixWord ++ tailWord_345860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345866 : List Nat := [3, 1, 2, 2, 1, 3, 1, 1, 3, 6]
def baseStart_345866 : Nat := 118140960795 + 345866 * 2 ^ 59
def prefixEnd_345866 : Nat := 4983230072969 + 3 ^ 40 * 345866 * 2
def baseEnd_345866 : Nat := 59198500016016343794799

theorem tailTrace_345866 : CollatzResearch.WordTrace tailWord_345866 prefixEnd_345866 59198500016016343794799 := by
  unfold tailWord_345866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3153692341248506513792363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8409846243329350703446301 3153692341248506513792363)
  ·
    refine ⟨4730538511872759770688545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3153692341248506513792363 4730538511872759770688545)
    ·
      refine ⟨3547903883904569828016409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4730538511872759770688545 3547903883904569828016409)
      ·
        refine ⟨2660927912928427371012307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3547903883904569828016409 2660927912928427371012307)
        ·
          refine ⟨3991391869392641056518461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2660927912928427371012307 3991391869392641056518461)
          ·
            refine ⟨1496771951022240396194423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3991391869392641056518461 1496771951022240396194423)
            ·
              refine ⟨2245157926533360594291635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496771951022240396194423 2245157926533360594291635)
              ·
                refine ⟨3367736889800040891437453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2245157926533360594291635 3367736889800040891437453)
                ·
                  refine ⟨1262901333675015334289045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3367736889800040891437453 1262901333675015334289045)
                  ·
                    refine ⟨59198500016016343794799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1262901333675015334289045 59198500016016343794799)
                    ·
                      rfl

theorem cell23_345866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_345866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345866 prefixEnd_345866 := by exact prefixLift 345866
  have htrace : WordTrace (prefixWord ++ tailWord_345866) baseStart_345866 baseEnd_345866 := by
    simpa [prefixWord, tailWord_345866, baseEnd_345866] using wordTrace_append hprefix tailTrace_345866
  have hstable : (prefixWord ++ tailWord_345866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345866).length < 2 ^ (prefixWord ++ tailWord_345866).sum := by decide
  have hdescent : baseEnd_345866 < baseStart_345866 := by decide
  rcases family_descends (prefixWord ++ tailWord_345866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345893 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 3, 2, 3]
def baseStart_345893 : Nat := 118140960795 + 345893 * 2 ^ 59
def prefixEnd_345893 : Nat := 4983230072969 + 3 ^ 40 * 345893 * 2
def baseEnd_345893 : Nat := 177609364025720425746773

theorem tailTrace_345893 : CollatzResearch.WordTrace tailWord_345893 prefixEnd_345893 177609364025720425746773 := by
  unfold tailWord_345893
  simp only [CollatzResearch.WordTrace]
  refine ⟨12615754135896209666402333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8410502757264139777601555 12615754135896209666402333)
  ·
    refine ⟨4730907800961078624900875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12615754135896209666402333 4730907800961078624900875)
    ·
      refine ⟨7096361701441617937351313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4730907800961078624900875 7096361701441617937351313)
      ·
        refine ⟨5322271276081213453013485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7096361701441617937351313 5322271276081213453013485)
        ·
          refine ⟨1995851728530455044880057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5322271276081213453013485 1995851728530455044880057)
          ·
            refine ⟨1496888796397841283660043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1995851728530455044880057 1496888796397841283660043)
            ·
              refine ⟨2245333194596761925490065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496888796397841283660043 2245333194596761925490065)
              ·
                refine ⟨1683999895947571444117549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2245333194596761925490065 1683999895947571444117549)
                ·
                  refine ⟨631499960980339291544081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1683999895947571444117549 631499960980339291544081)
                  ·
                    refine ⟨473624970735254468658061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 631499960980339291544081 473624970735254468658061)
                    ·
                      refine ⟨177609364025720425746773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 473624970735254468658061 177609364025720425746773)
                      ·
                        rfl

theorem cell23_345893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_345893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345893 prefixEnd_345893 := by exact prefixLift 345893
  have htrace : WordTrace (prefixWord ++ tailWord_345893) baseStart_345893 baseEnd_345893 := by
    simpa [prefixWord, tailWord_345893, baseEnd_345893] using wordTrace_append hprefix tailTrace_345893
  have hstable : (prefixWord ++ tailWord_345893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345893).length < 2 ^ (prefixWord ++ tailWord_345893).sum := by decide
  have hdescent : baseEnd_345893 < baseStart_345893 := by decide
  rcases family_descends (prefixWord ++ tailWord_345893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345907 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 3, 2, 2]
def baseStart_345907 : Nat := 118140960795 + 345907 * 2 ^ 59
def prefixEnd_345907 : Nat := 4983230072969 + 3 ^ 40 * 345907 * 2
def baseEnd_345907 : Nat := 177616552754883370971709

theorem tailTrace_345907 : CollatzResearch.WordTrace tailWord_345907 prefixEnd_345907 177616552754883370971709 := by
  unfold tailWord_345907
  simp only [CollatzResearch.WordTrace]
  refine ⟨12616264757845490057411975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8410843171896993371607983 12616264757845490057411975)
  ·
    refine ⟨18924397136768235086117963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12616264757845490057411975 18924397136768235086117963)
    ·
      refine ⟨28386595705152352629176945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18924397136768235086117963 28386595705152352629176945)
      ·
        refine ⟨21289946778864264471882709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28386595705152352629176945 21289946778864264471882709)
        ·
          refine ⟨498983127629631198559751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 21289946778864264471882709 498983127629631198559751)
          ·
            refine ⟨748474691444446797839627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498983127629631198559751 748474691444446797839627)
            ·
              refine ⟨1122712037166670196759441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748474691444446797839627 1122712037166670196759441)
              ·
                refine ⟨842034027875002647569581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1122712037166670196759441 842034027875002647569581)
                ·
                  refine ⟨315762760453125992838593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 842034027875002647569581 315762760453125992838593)
                  ·
                    refine ⟨236822070339844494628945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 315762760453125992838593 236822070339844494628945)
                    ·
                      refine ⟨177616552754883370971709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 236822070339844494628945 177616552754883370971709)
                      ·
                        rfl

theorem cell23_345907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 3, 2, 2].length) (baseStart_345907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345907 prefixEnd_345907 := by exact prefixLift 345907
  have htrace : WordTrace (prefixWord ++ tailWord_345907) baseStart_345907 baseEnd_345907 := by
    simpa [prefixWord, tailWord_345907, baseEnd_345907] using wordTrace_append hprefix tailTrace_345907
  have hstable : (prefixWord ++ tailWord_345907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345907).length < 2 ^ (prefixWord ++ tailWord_345907).sum := by decide
  have hdescent : baseEnd_345907 < baseStart_345907 := by decide
  rcases family_descends (prefixWord ++ tailWord_345907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345923 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 3]
def baseStart_345923 : Nat := 118140960795 + 345923 * 2 ^ 59
def prefixEnd_345923 : Nat := 4983230072969 + 3 ^ 40 * 345923 * 2
def baseEnd_345923 : Nat := 177624768445355308371635

theorem tailTrace_345923 : CollatzResearch.WordTrace tailWord_345923 prefixEnd_345923 177624768445355308371635 := by
  unfold tailWord_345923
  simp only [CollatzResearch.WordTrace]
  refine ⟨12616848325787524789994423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8411232217191683193329615 12616848325787524789994423)
  ·
    refine ⟨18925272488681287184991635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12616848325787524789994423 18925272488681287184991635)
    ·
      refine ⟨28387908733021930777487453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18925272488681287184991635 28387908733021930777487453)
      ·
        refine ⟨10645465774883224041557795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28387908733021930777487453 10645465774883224041557795)
        ·
          refine ⟨15968198662324836062336693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10645465774883224041557795 15968198662324836062336693)
          ·
            refine ⟨1497018624592953380844065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15968198662324836062336693 1497018624592953380844065)
            ·
              refine ⟨1122763968444715035633049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1497018624592953380844065 1122763968444715035633049)
              ·
                refine ⟨842072976333536276724787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1122763968444715035633049 842072976333536276724787)
                ·
                  refine ⟨1263109464500304415087181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842072976333536276724787 1263109464500304415087181)
                  ·
                    refine ⟨473666049187614155657693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1263109464500304415087181 473666049187614155657693)
                    ·
                      refine ⟨177624768445355308371635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 473666049187614155657693 177624768445355308371635)
                      ·
                        rfl

theorem cell23_345923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 3, 3].length) (baseStart_345923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345923 prefixEnd_345923 := by exact prefixLift 345923
  have htrace : WordTrace (prefixWord ++ tailWord_345923) baseStart_345923 baseEnd_345923 := by
    simpa [prefixWord, tailWord_345923, baseEnd_345923] using wordTrace_append hprefix tailTrace_345923
  have hstable : (prefixWord ++ tailWord_345923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345923).length < 2 ^ (prefixWord ++ tailWord_345923).sum := by decide
  have hdescent : baseEnd_345923 < baseStart_345923 := by decide
  rcases family_descends (prefixWord ++ tailWord_345923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345996 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 1, 1, 9]
def baseStart_345996 : Nat := 118140960795 + 345996 * 2 ^ 59
def prefixEnd_345996 : Nat := 4983230072969 + 3 ^ 40 * 345996 * 2
def baseEnd_345996 : Nat := 177662252533133522758799

theorem tailTrace_345996 : CollatzResearch.WordTrace tailWord_345996 prefixEnd_345996 177662252533133522758799 := by
  unfold tailWord_345996
  simp only [CollatzResearch.WordTrace]
  refine ⟨6309755427261529128700921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8413007236348705504934561 6309755427261529128700921)
  ·
    refine ⟨4732316570446146846525691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6309755427261529128700921 4732316570446146846525691)
    ·
      refine ⟨7098474855669220269788537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4732316570446146846525691 7098474855669220269788537)
      ·
        refine ⟨5323856141751915202341403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7098474855669220269788537 5323856141751915202341403)
        ·
          refine ⟨7985784212627872803512105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5323856141751915202341403 7985784212627872803512105)
          ·
            refine ⟨5989338159470904602634079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7985784212627872803512105 5989338159470904602634079)
            ·
              refine ⟨8984007239206356903951119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5989338159470904602634079 8984007239206356903951119)
              ·
                refine ⟨13476010858809535355926679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8984007239206356903951119 13476010858809535355926679)
                ·
                  refine ⟨20214016288214303033890019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13476010858809535355926679 20214016288214303033890019)
                  ·
                    refine ⟨30321024432321454550835029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20214016288214303033890019 30321024432321454550835029)
                    ·
                      refine ⟨177662252533133522758799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 30321024432321454550835029 177662252533133522758799)
                      ·
                        rfl

theorem cell23_345996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_345996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_345996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_345996 prefixEnd_345996 := by exact prefixLift 345996
  have htrace : WordTrace (prefixWord ++ tailWord_345996) baseStart_345996 baseEnd_345996 := by
    simpa [prefixWord, tailWord_345996, baseEnd_345996] using wordTrace_append hprefix tailTrace_345996
  have hstable : (prefixWord ++ tailWord_345996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345996).length < 2 ^ (prefixWord ++ tailWord_345996).sum := by decide
  have hdescent : baseEnd_345996 < baseStart_345996 := by decide
  rcases family_descends (prefixWord ++ tailWord_345996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346008 : List Nat := [2, 1, 2, 6, 2, 1, 2, 1, 2, 1, 3]
def baseStart_346008 : Nat := 118140960795 + 346008 * 2 ^ 59
def prefixEnd_346008 : Nat := 4983230072969 + 3 ^ 40 * 346008 * 2
def baseEnd_346008 : Nat := 177668414300987475808745

theorem tailTrace_346008 : CollatzResearch.WordTrace tailWord_346008 prefixEnd_346008 177668414300987475808745 := by
  unfold tailWord_346008
  simp only [CollatzResearch.WordTrace]
  refine ⟨6309974265239792153419339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8413299020319722871225785 6309974265239792153419339)
  ·
    refine ⟨9464961397859688230129009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6309974265239792153419339 9464961397859688230129009)
    ·
      refine ⟨7098721048394766172596757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9464961397859688230129009 7098721048394766172596757)
      ·
        refine ⟨332752549143504664340473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7098721048394766172596757 332752549143504664340473)
        ·
          refine ⟨249564411857628498255355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332752549143504664340473 249564411857628498255355)
          ·
            refine ⟨374346617786442747383033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249564411857628498255355 374346617786442747383033)
            ·
              refine ⟨280759963339832060537275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374346617786442747383033 280759963339832060537275)
              ·
                refine ⟨421139945009748090805913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280759963339832060537275 421139945009748090805913)
                ·
                  refine ⟨315854958757311068104435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421139945009748090805913 315854958757311068104435)
                  ·
                    refine ⟨473782438135966602156653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 315854958757311068104435 473782438135966602156653)
                    ·
                      refine ⟨177668414300987475808745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 473782438135966602156653 177668414300987475808745)
                      ·
                        rfl

theorem cell23_346008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_346008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346008 prefixEnd_346008 := by exact prefixLift 346008
  have htrace : WordTrace (prefixWord ++ tailWord_346008) baseStart_346008 baseEnd_346008 := by
    simpa [prefixWord, tailWord_346008, baseEnd_346008] using wordTrace_append hprefix tailTrace_346008
  have hstable : (prefixWord ++ tailWord_346008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346008).length < 2 ^ (prefixWord ++ tailWord_346008).sum := by decide
  have hdescent : baseEnd_346008 < baseStart_346008 := by decide
  rcases family_descends (prefixWord ++ tailWord_346008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346053 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 4, 1, 4]
def baseStart_346053 : Nat := 118140960795 + 346053 * 2 ^ 59
def prefixEnd_346053 : Nat := 4983230072969 + 3 ^ 40 * 346053 * 2
def baseEnd_346053 : Nat := 177691520930439799746037

theorem tailTrace_346053 : CollatzResearch.WordTrace tailWord_346053 prefixEnd_346053 177691520930439799746037 := by
  unfold tailWord_346053
  simp only [CollatzResearch.WordTrace]
  refine ⟨12621589815316556992226813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8414393210211037994817875 12621589815316556992226813)
  ·
    refine ⟨4733096180743708872085055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12621589815316556992226813 4733096180743708872085055)
    ·
      refine ⟨7099644271115563308127583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4733096180743708872085055 7099644271115563308127583)
      ·
        refine ⟨10649466406673344962191375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7099644271115563308127583 10649466406673344962191375)
        ·
          refine ⟨15974199610010017443287063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10649466406673344962191375 15974199610010017443287063)
          ·
            refine ⟨23961299415015026164930595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15974199610010017443287063 23961299415015026164930595)
            ·
              refine ⟨35941949122522539247395893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23961299415015026164930595 35941949122522539247395893)
              ·
                refine ⟨3369557730236488054443365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35941949122522539247395893 3369557730236488054443365)
                ·
                  refine ⟨631792074419341510208131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3369557730236488054443365 631792074419341510208131)
                  ·
                    refine ⟨947688111629012265312197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 631792074419341510208131 947688111629012265312197)
                    ·
                      refine ⟨177691520930439799746037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 947688111629012265312197 177691520930439799746037)
                      ·
                        rfl

theorem cell23_346053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_346053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346053 prefixEnd_346053 := by exact prefixLift 346053
  have htrace : WordTrace (prefixWord ++ tailWord_346053) baseStart_346053 baseEnd_346053 := by
    simpa [prefixWord, tailWord_346053, baseEnd_346053] using wordTrace_append hprefix tailTrace_346053
  have hstable : (prefixWord ++ tailWord_346053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346053).length < 2 ^ (prefixWord ++ tailWord_346053).sum := by decide
  have hdescent : baseEnd_346053 < baseStart_346053 := by decide
  rcases family_descends (prefixWord ++ tailWord_346053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346090 : List Nat := [3, 1, 3, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_346090 : Nat := 118140960795 + 346090 * 2 ^ 59
def prefixEnd_346090 : Nat := 4983230072969 + 3 ^ 40 * 346090 * 2
def baseEnd_346090 : Nat := 177710519714656154983367

theorem tailTrace_346090 : CollatzResearch.WordTrace tailWord_346090 prefixEnd_346090 177710519714656154983367 := by
  unfold tailWord_346090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3155734829045628077830931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8415292877455008207549149 3155734829045628077830931)
  ·
    refine ⟨4733602243568442116746397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3155734829045628077830931 4733602243568442116746397)
    ·
      refine ⟨1775100841338165793779899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4733602243568442116746397 1775100841338165793779899)
      ·
        refine ⟨2662651262007248690669849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1775100841338165793779899 2662651262007248690669849)
        ·
          refine ⟨1996988446505436518002387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2662651262007248690669849 1996988446505436518002387)
          ·
            refine ⟨2995482669758154777003581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1996988446505436518002387 2995482669758154777003581)
            ·
              refine ⟨1123306001159308041376343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2995482669758154777003581 1123306001159308041376343)
              ·
                refine ⟨1684959001738962062064515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1123306001159308041376343 1684959001738962062064515)
                ·
                  refine ⟨2527438502608443093096773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1684959001738962062064515 2527438502608443093096773)
                  ·
                    refine ⟨473894719239083079955645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2527438502608443093096773 473894719239083079955645)
                    ·
                      refine ⟨177710519714656154983367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 473894719239083079955645 177710519714656154983367)
                      ·
                        rfl

theorem cell23_346090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_346090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346090 prefixEnd_346090 := by exact prefixLift 346090
  have htrace : WordTrace (prefixWord ++ tailWord_346090) baseStart_346090 baseEnd_346090 := by
    simpa [prefixWord, tailWord_346090, baseEnd_346090] using wordTrace_append hprefix tailTrace_346090
  have hstable : (prefixWord ++ tailWord_346090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346090).length < 2 ^ (prefixWord ++ tailWord_346090).sum := by decide
  have hdescent : baseEnd_346090 < baseStart_346090 := by decide
  rcases family_descends (prefixWord ++ tailWord_346090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346103 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 3]
def baseStart_346103 : Nat := 118140960795 + 346103 * 2 ^ 59
def prefixEnd_346103 : Nat := 4983230072969 + 3 ^ 40 * 346103 * 2
def baseEnd_346103 : Nat := 177717194963164604120807

theorem tailTrace_346103 : CollatzResearch.WordTrace tailWord_346103 prefixEnd_346103 177717194963164604120807 := by
  unfold tailWord_346103
  simp only [CollatzResearch.WordTrace]
  refine ⟨12623413465135415531546963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8415608976756943687697975 12623413465135415531546963)
  ·
    refine ⟨18935120197703123297320445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12623413465135415531546963 18935120197703123297320445)
    ·
      refine ⟨7100670074138671236495167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18935120197703123297320445 7100670074138671236495167)
      ·
        refine ⟨10651005111208006854742751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7100670074138671236495167 10651005111208006854742751)
        ·
          refine ⟨15976507666812010282114127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10651005111208006854742751 15976507666812010282114127)
          ·
            refine ⟨23964761500218015423171191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15976507666812010282114127 23964761500218015423171191)
            ·
              refine ⟨35947142250327023134756787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23964761500218015423171191 35947142250327023134756787)
              ·
                refine ⟨53920713375490534702135181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35947142250327023134756787 53920713375490534702135181)
                ·
                  refine ⟨20220267515808950513300693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53920713375490534702135181 20220267515808950513300693)
                  ·
                    refine ⟨473912519901772277655485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20220267515808950513300693 473912519901772277655485)
                    ·
                      refine ⟨177717194963164604120807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 473912519901772277655485 177717194963164604120807)
                      ·
                        rfl

theorem cell23_346103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_346103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346103 prefixEnd_346103 := by exact prefixLift 346103
  have htrace : WordTrace (prefixWord ++ tailWord_346103) baseStart_346103 baseEnd_346103 := by
    simpa [prefixWord, tailWord_346103, baseEnd_346103] using wordTrace_append hprefix tailTrace_346103
  have hstable : (prefixWord ++ tailWord_346103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346103).length < 2 ^ (prefixWord ++ tailWord_346103).sum := by decide
  have hdescent : baseEnd_346103 < baseStart_346103 := by decide
  rcases family_descends (prefixWord ++ tailWord_346103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346113 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_346113 : Nat := 118140960795 + 346113 * 2 ^ 59
def prefixEnd_346113 : Nat := 4983230072969 + 3 ^ 40 * 346113 * 2
def baseEnd_346113 : Nat := 177722329769709564995761

theorem tailTrace_346113 : CollatzResearch.WordTrace tailWord_346113 prefixEnd_346113 177722329769709564995761 := by
  unfold tailWord_346113
  simp only [CollatzResearch.WordTrace]
  refine ⟨12623778195099187239410993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8415852130066124826273995 12623778195099187239410993)
  ·
    refine ⟨9467833646324390429558245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12623778195099187239410993 9467833646324390429558245)
    ·
      refine ⟨1775218808685823205542171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9467833646324390429558245 1775218808685823205542171)
      ·
        refine ⟨2662828213028734808313257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1775218808685823205542171 2662828213028734808313257)
        ·
          refine ⟨1997121159771551106234943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2662828213028734808313257 1997121159771551106234943)
          ·
            refine ⟨2995681739657326659352415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1997121159771551106234943 2995681739657326659352415)
            ·
              refine ⟨4493522609485989989028623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2995681739657326659352415 4493522609485989989028623)
              ·
                refine ⟨6740283914228984983542935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4493522609485989989028623 6740283914228984983542935)
                ·
                  refine ⟨10110425871343477475314403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6740283914228984983542935 10110425871343477475314403)
                  ·
                    refine ⟨15165638807015216212971605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10110425871343477475314403 15165638807015216212971605)
                    ·
                      refine ⟨177722329769709564995761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 15165638807015216212971605 177722329769709564995761)
                      ·
                        rfl

theorem cell23_346113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_346113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346113 prefixEnd_346113 := by exact prefixLift 346113
  have htrace : WordTrace (prefixWord ++ tailWord_346113) baseStart_346113 baseEnd_346113 := by
    simpa [prefixWord, tailWord_346113, baseEnd_346113] using wordTrace_append hprefix tailTrace_346113
  have hstable : (prefixWord ++ tailWord_346113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346113).length < 2 ^ (prefixWord ++ tailWord_346113).sum := by decide
  have hdescent : baseEnd_346113 < baseStart_346113 := by decide
  rcases family_descends (prefixWord ++ tailWord_346113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346147 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 2, 3, 2]
def baseStart_346147 : Nat := 118140960795 + 346147 * 2 ^ 59
def prefixEnd_346147 : Nat := 4983230072969 + 3 ^ 40 * 346147 * 2
def baseEnd_346147 : Nat := 177739788111962431970605

theorem tailTrace_346147 : CollatzResearch.WordTrace tailWord_346147 prefixEnd_346147 177739788111962431970605 := by
  unfold tailWord_346147
  simp only [CollatzResearch.WordTrace]
  refine ⟨12625018276976011046148695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8416678851317340697432463 12625018276976011046148695)
  ·
    refine ⟨18937527415464016569223043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12625018276976011046148695 18937527415464016569223043)
    ·
      refine ⟨28406291123196024853834565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18937527415464016569223043 28406291123196024853834565)
      ·
        refine ⟨5326179585599254660093981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28406291123196024853834565 5326179585599254660093981)
        ·
          refine ⟨1997317344599720497535243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5326179585599254660093981 1997317344599720497535243)
          ·
            refine ⟨2995976016899580746302865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1997317344599720497535243 2995976016899580746302865)
            ·
              refine ⟨2246982012674685559727149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2995976016899580746302865 2246982012674685559727149)
              ·
                refine ⟨842618254753007084897681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2246982012674685559727149 842618254753007084897681)
                ·
                  refine ⟨631963691064755313673261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 842618254753007084897681 631963691064755313673261)
                  ·
                    refine ⟨236986384149283242627473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 631963691064755313673261 236986384149283242627473)
                    ·
                      refine ⟨177739788111962431970605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 236986384149283242627473 177739788111962431970605)
                      ·
                        rfl

theorem cell23_346147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_346147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346147 prefixEnd_346147 := by exact prefixLift 346147
  have htrace : WordTrace (prefixWord ++ tailWord_346147) baseStart_346147 baseEnd_346147 := by
    simpa [prefixWord, tailWord_346147, baseEnd_346147] using wordTrace_append hprefix tailTrace_346147
  have hstable : (prefixWord ++ tailWord_346147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346147).length < 2 ^ (prefixWord ++ tailWord_346147).sum := by decide
  have hdescent : baseEnd_346147 < baseStart_346147 := by decide
  rcases family_descends (prefixWord ++ tailWord_346147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346148 : List Nat := [2, 3, 1, 4, 3, 1, 1, 3, 1, 4]
def baseStart_346148 : Nat := 118140960795 + 346148 * 2 ^ 59
def prefixEnd_346148 : Nat := 4983230072969 + 3 ^ 40 * 346148 * 2
def baseEnd_346148 : Nat := 59246767197538976019367

theorem tailTrace_346148 : CollatzResearch.WordTrace tailWord_346148 prefixEnd_346148 59246767197538976019367 := by
  unfold tailWord_346148
  simp only [CollatzResearch.WordTrace]
  refine ⟨6312527374986194108467549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8416703166648258811290065 6312527374986194108467549)
  ·
    refine ⟨2367197765619822790675331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6312527374986194108467549 2367197765619822790675331)
    ·
      refine ⟨3550796648429734186012997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2367197765619822790675331 3550796648429734186012997)
      ·
        refine ⟨665774371580575159877437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3550796648429734186012997 665774371580575159877437)
        ·
          refine ⟨249665389342715684954039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 665774371580575159877437 249665389342715684954039)
          ·
            refine ⟨374498084014073527431059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249665389342715684954039 374498084014073527431059)
            ·
              refine ⟨561747126021110291146589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374498084014073527431059 561747126021110291146589)
              ·
                refine ⟨210655172257916359179971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 561747126021110291146589 210655172257916359179971)
                ·
                  refine ⟨315982758386874538769957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210655172257916359179971 315982758386874538769957)
                  ·
                    refine ⟨59246767197538976019367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 315982758386874538769957 59246767197538976019367)
                    ·
                      rfl

theorem cell23_346148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_346148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346148 prefixEnd_346148 := by exact prefixLift 346148
  have htrace : WordTrace (prefixWord ++ tailWord_346148) baseStart_346148 baseEnd_346148 := by
    simpa [prefixWord, tailWord_346148, baseEnd_346148] using wordTrace_append hprefix tailTrace_346148
  have hstable : (prefixWord ++ tailWord_346148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346148).length < 2 ^ (prefixWord ++ tailWord_346148).sum := by decide
  have hdescent : baseEnd_346148 < baseStart_346148 := by decide
  rcases family_descends (prefixWord ++ tailWord_346148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346190 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6]
def baseStart_346190 : Nat := 118140960795 + 346190 * 2 ^ 59
def prefixEnd_346190 : Nat := 4983230072969 + 3 ^ 40 * 346190 * 2
def baseEnd_346190 : Nat := 177761867780105763732907

theorem tailTrace_346190 : CollatzResearch.WordTrace tailWord_346190 prefixEnd_346190 177761867780105763732907 := by
  unfold tailWord_346190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1578323326977528673745503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8417724410546819593309349 1578323326977528673745503)
  ·
    refine ⟨2367484990466293010618255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1578323326977528673745503 2367484990466293010618255)
    ·
      refine ⟨3551227485699439515927383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2367484990466293010618255 3551227485699439515927383)
      ·
        refine ⟨5326841228549159273891075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3551227485699439515927383 5326841228549159273891075)
        ·
          refine ⟨7990261842823738910836613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5326841228549159273891075 7990261842823738910836613)
          ·
            refine ⟨1498174095529451045781865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7990261842823738910836613 1498174095529451045781865)
            ·
              refine ⟨1123630571647088284336399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1498174095529451045781865 1123630571647088284336399)
              ·
                refine ⟨1685445857470632426504599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1123630571647088284336399 1685445857470632426504599)
                ·
                  refine ⟨2528168786205948639756899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1685445857470632426504599 2528168786205948639756899)
                  ·
                    refine ⟨3792253179308922959635349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2528168786205948639756899 3792253179308922959635349)
                    ·
                      refine ⟨177761867780105763732907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3792253179308922959635349 177761867780105763732907)
                      ·
                        rfl

theorem cell23_346190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 1, 1, 6].length) (baseStart_346190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346190 prefixEnd_346190 := by exact prefixLift 346190
  have htrace : WordTrace (prefixWord ++ tailWord_346190) baseStart_346190 baseEnd_346190 := by
    simpa [prefixWord, tailWord_346190, baseEnd_346190] using wordTrace_append hprefix tailTrace_346190
  have hstable : (prefixWord ++ tailWord_346190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346190).length < 2 ^ (prefixWord ++ tailWord_346190).sum := by decide
  have hdescent : baseEnd_346190 < baseStart_346190 := by decide
  rcases family_descends (prefixWord ++ tailWord_346190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346197 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 3, 2, 3]
def baseStart_346197 : Nat := 118140960795 + 346197 * 2 ^ 59
def prefixEnd_346197 : Nat := 4983230072969 + 3 ^ 40 * 346197 * 2
def baseEnd_346197 : Nat := 177765462144687236345375

theorem tailTrace_346197 : CollatzResearch.WordTrace tailWord_346197 prefixEnd_346197 177765462144687236345375 := by
  unfold tailWord_346197
  simp only [CollatzResearch.WordTrace]
  refine ⟨12626841926794869585468845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8417894617863246390312563 12626841926794869585468845)
  ·
    refine ⟨4735065722548076094550817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12626841926794869585468845 4735065722548076094550817)
    ·
      refine ⟨3551299291911057070913113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4735065722548076094550817 3551299291911057070913113)
      ·
        refine ⟨2663474468933292803184835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3551299291911057070913113 2663474468933292803184835)
        ·
          refine ⟨3995211703399939204777253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2663474468933292803184835 3995211703399939204777253)
          ·
            refine ⟨749102194387488600895735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3995211703399939204777253 749102194387488600895735)
            ·
              refine ⟨1123653291581232901343603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749102194387488600895735 1123653291581232901343603)
              ·
                refine ⟨1685479937371849352015405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1123653291581232901343603 1685479937371849352015405)
                ·
                  refine ⟨632054976514443507005777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1685479937371849352015405 632054976514443507005777)
                  ·
                    refine ⟨474041232385832630254333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 632054976514443507005777 474041232385832630254333)
                    ·
                      refine ⟨177765462144687236345375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 474041232385832630254333 177765462144687236345375)
                      ·
                        rfl

theorem cell23_346197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_346197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346197 prefixEnd_346197 := by exact prefixLift 346197
  have htrace : WordTrace (prefixWord ++ tailWord_346197) baseStart_346197 baseEnd_346197 := by
    simpa [prefixWord, tailWord_346197, baseEnd_346197] using wordTrace_append hprefix tailTrace_346197
  have hstable : (prefixWord ++ tailWord_346197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346197).length < 2 ^ (prefixWord ++ tailWord_346197).sum := by decide
  have hdescent : baseEnd_346197 < baseStart_346197 := by decide
  rcases family_descends (prefixWord ++ tailWord_346197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346198 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_346198 : Nat := 118140960795 + 346198 * 2 ^ 59
def prefixEnd_346198 : Nat := 4983230072969 + 3 ^ 40 * 346198 * 2
def baseEnd_346198 : Nat := 177765975625341732432871

theorem tailTrace_346198 : CollatzResearch.WordTrace tailWord_346198 prefixEnd_346198 177765975625341732432871 := by
  unfold tailWord_346198
  simp only [CollatzResearch.WordTrace]
  refine ⟨789179899986952922265953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8417918933194164504170165 789179899986952922265953)
  ·
    refine ⟨591884924990214691699465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 789179899986952922265953 591884924990214691699465)
    ·
      refine ⟨443913693742661018774599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 591884924990214691699465 443913693742661018774599)
      ·
        refine ⟨665870540613991528161899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443913693742661018774599 665870540613991528161899)
        ·
          refine ⟨998805810920987292242849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665870540613991528161899 998805810920987292242849)
          ·
            refine ⟨749104358190740469182137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 998805810920987292242849 749104358190740469182137)
            ·
              refine ⟨561828268643055351886603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 749104358190740469182137 561828268643055351886603)
              ·
                refine ⟨842742402964583027829905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561828268643055351886603 842742402964583027829905)
                ·
                  refine ⟨632056802223437270872429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 842742402964583027829905 632056802223437270872429)
                  ·
                    refine ⟨237021300833788976577161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 632056802223437270872429 237021300833788976577161)
                    ·
                      refine ⟨177765975625341732432871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 237021300833788976577161 177765975625341732432871)
                      ·
                        rfl

theorem cell23_346198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_346198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346198 prefixEnd_346198 := by exact prefixLift 346198
  have htrace : WordTrace (prefixWord ++ tailWord_346198) baseStart_346198 baseEnd_346198 := by
    simpa [prefixWord, tailWord_346198, baseEnd_346198] using wordTrace_append hprefix tailTrace_346198
  have hstable : (prefixWord ++ tailWord_346198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346198).length < 2 ^ (prefixWord ++ tailWord_346198).sum := by decide
  have hdescent : baseEnd_346198 < baseStart_346198 := by decide
  rcases family_descends (prefixWord ++ tailWord_346198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346244 : List Nat := [2, 3, 2, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_346244 : Nat := 118140960795 + 346244 * 2 ^ 59
def prefixEnd_346244 : Nat := 4983230072969 + 3 ^ 40 * 346244 * 2
def baseEnd_346244 : Nat := 177789595735448552457659

theorem tailTrace_346244 : CollatzResearch.WordTrace tailWord_346244 prefixEnd_346244 177789595735448552457659 := by
  unfold tailWord_346244
  simp only [CollatzResearch.WordTrace]
  refine ⟨6314278078812298306214893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8419037438416397741619857 6314278078812298306214893)
  ·
    refine ⟨2367854279554611864830585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6314278078812298306214893 2367854279554611864830585)
    ·
      refine ⟨1775890709665958898622939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2367854279554611864830585 1775890709665958898622939)
      ·
        refine ⟨2663836064498938347934409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1775890709665958898622939 2663836064498938347934409)
        ·
          refine ⟨1997877048374203760950807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2663836064498938347934409 1997877048374203760950807)
          ·
            refine ⟨2996815572561305641426211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1997877048374203760950807 2996815572561305641426211)
            ·
              refine ⟨4495223358841958462139317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2996815572561305641426211 4495223358841958462139317)
              ·
                refine ⟨421427189891433605825561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4495223358841958462139317 421427189891433605825561)
                ·
                  refine ⟨316070392418575204369171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421427189891433605825561 316070392418575204369171)
                  ·
                    refine ⟨474105588627862806553757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 316070392418575204369171 474105588627862806553757)
                    ·
                      refine ⟨177789595735448552457659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 474105588627862806553757 177789595735448552457659)
                      ·
                        rfl

theorem cell23_346244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_346244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346244 prefixEnd_346244 := by exact prefixLift 346244
  have htrace : WordTrace (prefixWord ++ tailWord_346244) baseStart_346244 baseEnd_346244 := by
    simpa [prefixWord, tailWord_346244, baseEnd_346244] using wordTrace_append hprefix tailTrace_346244
  have hstable : (prefixWord ++ tailWord_346244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346244).length < 2 ^ (prefixWord ++ tailWord_346244).sum := by decide
  have hdescent : baseEnd_346244 < baseStart_346244 := by decide
  rcases family_descends (prefixWord ++ tailWord_346244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346267 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 1, 4, 2]
def baseStart_346267 : Nat := 118140960795 + 346267 * 2 ^ 59
def prefixEnd_346267 : Nat := 4983230072969 + 3 ^ 40 * 346267 * 2
def baseEnd_346267 : Nat := 177801405790501962470053

theorem tailTrace_346267 : CollatzResearch.WordTrace tailWord_346267 prefixEnd_346267 177801405790501962470053 := by
  unfold tailWord_346267
  simp only [CollatzResearch.WordTrace]
  refine ⟨12629395036541271540517055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8419596691027514360344703 12629395036541271540517055)
  ·
    refine ⟨18944092554811907310775583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12629395036541271540517055 18944092554811907310775583)
    ·
      refine ⟨28416138832217860966163375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18944092554811907310775583 28416138832217860966163375)
      ·
        refine ⟨42624208248326791449245063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28416138832217860966163375 42624208248326791449245063)
        ·
          refine ⟨63936312372490187173867595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42624208248326791449245063 63936312372490187173867595)
          ·
            refine ⟨95904468558735280760801393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63936312372490187173867595 95904468558735280760801393)
            ·
              refine ⟨71928351419051460570601045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95904468558735280760801393 71928351419051460570601045)
              ·
                refine ⟨842910368192009303561731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 71928351419051460570601045 842910368192009303561731)
                ·
                  refine ⟨1264365552288013955342597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 842910368192009303561731 1264365552288013955342597)
                  ·
                    refine ⟨237068541054002616626737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1264365552288013955342597 237068541054002616626737)
                    ·
                      refine ⟨177801405790501962470053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 237068541054002616626737 177801405790501962470053)
                      ·
                        rfl

theorem cell23_346267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 4, 2].length) (baseStart_346267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346267 prefixEnd_346267 := by exact prefixLift 346267
  have htrace : WordTrace (prefixWord ++ tailWord_346267) baseStart_346267 baseEnd_346267 := by
    simpa [prefixWord, tailWord_346267, baseEnd_346267] using wordTrace_append hprefix tailTrace_346267
  have hstable : (prefixWord ++ tailWord_346267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346267).length < 2 ^ (prefixWord ++ tailWord_346267).sum := by decide
  have hdescent : baseEnd_346267 < baseStart_346267 := by decide
  rcases family_descends (prefixWord ++ tailWord_346267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346271 : List Nat := [1, 1, 2, 6, 1, 2, 1, 3, 1, 3, 2]
def baseStart_346271 : Nat := 118140960795 + 346271 * 2 ^ 59
def prefixEnd_346271 : Nat := 4983230072969 + 3 ^ 40 * 346271 * 2
def baseEnd_346271 : Nat := 177803459713119946820035

theorem tailTrace_346271 : CollatzResearch.WordTrace tailWord_346271 prefixEnd_346271 177803459713119946820035 := by
  unfold tailWord_346271
  simp only [CollatzResearch.WordTrace]
  refine ⟨12629540928526780223662667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8419693952351186815775111 12629540928526780223662667)
  ·
    refine ⟨18944311392790170335494001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12629540928526780223662667 18944311392790170335494001)
    ·
      refine ⟨14208233544592627751620501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18944311392790170335494001 14208233544592627751620501)
      ·
        refine ⟨666010947402779425857211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14208233544592627751620501 666010947402779425857211)
        ·
          refine ⟨999016421104169138785817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666010947402779425857211 999016421104169138785817)
          ·
            refine ⟨749262315828126854089363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 999016421104169138785817 749262315828126854089363)
            ·
              refine ⟨1123893473742190281134045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749262315828126854089363 1123893473742190281134045)
              ·
                refine ⟨421460052653321355425267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1123893473742190281134045 421460052653321355425267)
                ·
                  refine ⟨632190078979982033137901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421460052653321355425267 632190078979982033137901)
                  ·
                    refine ⟨237071279617493262426713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 632190078979982033137901 237071279617493262426713)
                    ·
                      refine ⟨177803459713119946820035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 237071279617493262426713 177803459713119946820035)
                      ·
                        rfl

theorem cell23_346271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_346271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346271 prefixEnd_346271 := by exact prefixLift 346271
  have htrace : WordTrace (prefixWord ++ tailWord_346271) baseStart_346271 baseEnd_346271 := by
    simpa [prefixWord, tailWord_346271, baseEnd_346271] using wordTrace_append hprefix tailTrace_346271
  have hstable : (prefixWord ++ tailWord_346271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346271).length < 2 ^ (prefixWord ++ tailWord_346271).sum := by decide
  have hdescent : baseEnd_346271 < baseStart_346271 := by decide
  rcases family_descends (prefixWord ++ tailWord_346271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346320 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 8, 5]
def baseStart_346320 : Nat := 118140960795 + 346320 * 2 ^ 59
def prefixEnd_346320 : Nat := 4983230072969 + 3 ^ 40 * 346320 * 2
def baseEnd_346320 : Nat := 59276206755063418369103

theorem tailTrace_346320 : CollatzResearch.WordTrace tailWord_346320 prefixEnd_346320 59276206755063418369103 := by
  unfold tailWord_346320
  simp only [CollatzResearch.WordTrace]
  refine ⟨6315664052674630796098207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8420885403566174394797609 6315664052674630796098207)
  ·
    refine ⟨9473496079011946194147311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6315664052674630796098207 9473496079011946194147311)
    ·
      refine ⟨14210244118517919291220967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9473496079011946194147311 14210244118517919291220967)
      ·
        refine ⟨21315366177776878936831451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14210244118517919291220967 21315366177776878936831451)
        ·
          refine ⟨31973049266665318405247177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21315366177776878936831451 31973049266665318405247177)
          ·
            refine ⟨23979786949998988803935383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31973049266665318405247177 23979786949998988803935383)
            ·
              refine ⟨35969680424998483205903075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23979786949998988803935383 35969680424998483205903075)
              ·
                refine ⟨53954520637497724808854613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35969680424998483205903075 53954520637497724808854613)
                ·
                  refine ⟨632279538720676462603765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 53954520637497724808854613 632279538720676462603765)
                  ·
                    refine ⟨59276206755063418369103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 632279538720676462603765 59276206755063418369103)
                    ·
                      rfl

theorem cell23_346320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 8, 5].length) (baseStart_346320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346320 prefixEnd_346320 := by exact prefixLift 346320
  have htrace : WordTrace (prefixWord ++ tailWord_346320) baseStart_346320 baseEnd_346320 := by
    simpa [prefixWord, tailWord_346320, baseEnd_346320] using wordTrace_append hprefix tailTrace_346320
  have hstable : (prefixWord ++ tailWord_346320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346320).length < 2 ^ (prefixWord ++ tailWord_346320).sum := by decide
  have hdescent : baseEnd_346320 < baseStart_346320 := by decide
  rcases family_descends (prefixWord ++ tailWord_346320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346327 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 1, 7, 2]
def baseStart_346327 : Nat := 118140960795 + 346327 * 2 ^ 59
def prefixEnd_346327 : Nat := 4983230072969 + 3 ^ 40 * 346327 * 2
def baseEnd_346327 : Nat := 177832214629771727719777

theorem tailTrace_346327 : CollatzResearch.WordTrace tailWord_346327 prefixEnd_346327 177832214629771727719777 := by
  unfold tailWord_346327
  simp only [CollatzResearch.WordTrace]
  refine ⟨12631583416323901787701235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8421055610882601191800823 12631583416323901787701235)
  ·
    refine ⟨18947375124485852681551853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12631583416323901787701235 18947375124485852681551853)
    ·
      refine ⟨7105265671682194755581945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18947375124485852681551853 7105265671682194755581945)
      ·
        refine ⟨5328949253761646066686459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7105265671682194755581945 5328949253761646066686459)
        ·
          refine ⟨7993423880642469100029689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5328949253761646066686459 7993423880642469100029689)
          ·
            refine ⟨5995067910481851825022267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7993423880642469100029689 5995067910481851825022267)
            ·
              refine ⟨8992601865722777737533401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5995067910481851825022267 8992601865722777737533401)
              ·
                refine ⟨6744451399292083303150051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8992601865722777737533401 6744451399292083303150051)
                ·
                  refine ⟨10116677098938124954725077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6744451399292083303150051 10116677098938124954725077)
                  ·
                    refine ⟨237109619506362303626369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10116677098938124954725077 237109619506362303626369)
                    ·
                      refine ⟨177832214629771727719777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 237109619506362303626369 177832214629771727719777)
                      ·
                        rfl

theorem cell23_346327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 7, 2].length) (baseStart_346327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346327 prefixEnd_346327 := by exact prefixLift 346327
  have htrace : WordTrace (prefixWord ++ tailWord_346327) baseStart_346327 baseEnd_346327 := by
    simpa [prefixWord, tailWord_346327, baseEnd_346327] using wordTrace_append hprefix tailTrace_346327
  have hstable : (prefixWord ++ tailWord_346327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346327).length < 2 ^ (prefixWord ++ tailWord_346327).sum := by decide
  have hdescent : baseEnd_346327 < baseStart_346327 := by decide
  rcases family_descends (prefixWord ++ tailWord_346327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346337 : List Nat := [1, 2, 3, 1, 3, 1, 3, 2, 2, 5]
def baseStart_346337 : Nat := 118140960795 + 346337 * 2 ^ 59
def prefixEnd_346337 : Nat := 4983230072969 + 3 ^ 40 * 346337 * 2
def baseEnd_346337 : Nat := 59279116478772229531577

theorem tailTrace_346337 : CollatzResearch.WordTrace tailWord_346337 prefixEnd_346337 59279116478772229531577 := by
  unfold tailWord_346337
  simp only [CollatzResearch.WordTrace]
  refine ⟨12631948146287673495565265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8421298764191782330376843 12631948146287673495565265)
  ·
    refine ⟨9473961109715755121673949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12631948146287673495565265 9473961109715755121673949)
    ·
      refine ⟨3552735416143408170627731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9473961109715755121673949 3552735416143408170627731)
      ·
        refine ⟨5329103124215112255941597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3552735416143408170627731 5329103124215112255941597)
        ·
          refine ⟨1998413671580667095978099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5329103124215112255941597 1998413671580667095978099)
          ·
            refine ⟨2997620507371000643967149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1998413671580667095978099 2997620507371000643967149)
            ·
              refine ⟨1124107690264125241487681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2997620507371000643967149 1124107690264125241487681)
              ·
                refine ⟨843080767698093931115761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1124107690264125241487681 843080767698093931115761)
                ·
                  refine ⟨632310575773570448336821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 843080767698093931115761 632310575773570448336821)
                  ·
                    refine ⟨59279116478772229531577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 632310575773570448336821 59279116478772229531577)
                    ·
                      rfl

theorem cell23_346337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_346337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346337 prefixEnd_346337 := by exact prefixLift 346337
  have htrace : WordTrace (prefixWord ++ tailWord_346337) baseStart_346337 baseEnd_346337 := by
    simpa [prefixWord, tailWord_346337, baseEnd_346337] using wordTrace_append hprefix tailTrace_346337
  have hstable : (prefixWord ++ tailWord_346337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346337).length < 2 ^ (prefixWord ++ tailWord_346337).sum := by decide
  have hdescent : baseEnd_346337 < baseStart_346337 := by decide
  rcases family_descends (prefixWord ++ tailWord_346337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346341 : List Nat := [1, 3, 1, 4, 2, 2, 3, 2, 5]
def baseStart_346341 : Nat := 118140960795 + 346341 * 2 ^ 59
def prefixEnd_346341 : Nat := 4983230072969 + 3 ^ 40 * 346341 * 2
def baseEnd_346341 : Nat := 19759933706548296993857

theorem tailTrace_346341 : CollatzResearch.WordTrace tailWord_346341 prefixEnd_346341 19759933706548296993857 := by
  unfold tailWord_346341
  simp only [CollatzResearch.WordTrace]
  refine ⟨12632094038273182178710877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8421396025515454785807251 12632094038273182178710877)
  ·
    refine ⟨4737035264352443317016579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12632094038273182178710877 4737035264352443317016579)
    ·
      refine ⟨7105552896528664975524869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4737035264352443317016579 7105552896528664975524869)
      ·
        refine ⟨1332291168099124682910913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7105552896528664975524869 1332291168099124682910913)
        ·
          refine ⟨999218376074343512183185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1332291168099124682910913 999218376074343512183185)
          ·
            refine ⟨749413782055757634137389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 999218376074343512183185 749413782055757634137389)
            ·
              refine ⟨281030168270909112801521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 749413782055757634137389 281030168270909112801521)
              ·
                refine ⟨210772626203181834601141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281030168270909112801521 210772626203181834601141)
                ·
                  refine ⟨19759933706548296993857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 210772626203181834601141 19759933706548296993857)
                  ·
                    rfl

theorem cell23_346341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 5].length) (baseStart_346341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346341 prefixEnd_346341 := by exact prefixLift 346341
  have htrace : WordTrace (prefixWord ++ tailWord_346341) baseStart_346341 baseEnd_346341 := by
    simpa [prefixWord, tailWord_346341, baseEnd_346341] using wordTrace_append hprefix tailTrace_346341
  have hstable : (prefixWord ++ tailWord_346341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346341).length < 2 ^ (prefixWord ++ tailWord_346341).sum := by decide
  have hdescent : baseEnd_346341 < baseStart_346341 := by decide
  rcases family_descends (prefixWord ++ tailWord_346341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346360 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 1, 5, 5]
def baseStart_346360 : Nat := 118140960795 + 346360 * 2 ^ 59
def prefixEnd_346360 : Nat := 4983230072969 + 3 ^ 40 * 346360 * 2
def baseEnd_346360 : Nat := 177849159491370098607125

theorem tailTrace_346360 : CollatzResearch.WordTrace tailWord_346360 prefixEnd_346360 177849159491370098607125 := by
  unfold tailWord_346360
  simp only [CollatzResearch.WordTrace]
  refine ⟨6316393512602174211826267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8421858016802898949101689 6316393512602174211826267)
  ·
    refine ⟨9474590268903261317739401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6316393512602174211826267 9474590268903261317739401)
    ·
      refine ⟨7105942701677445988304551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9474590268903261317739401 7105942701677445988304551)
      ·
        refine ⟨10658914052516168982456827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7105942701677445988304551 10658914052516168982456827)
        ·
          refine ⟨15988371078774253473685241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10658914052516168982456827 15988371078774253473685241)
          ·
            refine ⟨11991278309080690105263931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15988371078774253473685241 11991278309080690105263931)
            ·
              refine ⟨17986917463621035157895897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11991278309080690105263931 17986917463621035157895897)
              ·
                refine ⟨13490188097715776368421923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17986917463621035157895897 13490188097715776368421923)
                ·
                  refine ⟨20235282146573664552632885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13490188097715776368421923 20235282146573664552632885)
                  ·
                    refine ⟨1897057701241281051809333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20235282146573664552632885 1897057701241281051809333)
                    ·
                      refine ⟨177849159491370098607125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1897057701241281051809333 177849159491370098607125)
                      ·
                        rfl

theorem cell23_346360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_346360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346360 prefixEnd_346360 := by exact prefixLift 346360
  have htrace : WordTrace (prefixWord ++ tailWord_346360) baseStart_346360 baseEnd_346360 := by
    simpa [prefixWord, tailWord_346360, baseEnd_346360] using wordTrace_append hprefix tailTrace_346360
  have hstable : (prefixWord ++ tailWord_346360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346360).length < 2 ^ (prefixWord ++ tailWord_346360).sum := by decide
  have hdescent : baseEnd_346360 < baseStart_346360 := by decide
  rcases family_descends (prefixWord ++ tailWord_346360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346367 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 5, 4]
def baseStart_346367 : Nat := 118140960795 + 346367 * 2 ^ 59
def prefixEnd_346367 : Nat := 4983230072969 + 3 ^ 40 * 346367 * 2
def baseEnd_346367 : Nat := 59284251285317190406531

theorem tailTrace_346367 : CollatzResearch.WordTrace tailWord_346367 prefixEnd_346367 59284251285317190406531 := by
  unfold tailWord_346367
  simp only [CollatzResearch.WordTrace]
  refine ⟨12633042336178988619157355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8422028224119325746104903 12633042336178988619157355)
  ·
    refine ⟨18949563504268482928736033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12633042336178988619157355 18949563504268482928736033)
    ·
      refine ⟨14212172628201362196552025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18949563504268482928736033 14212172628201362196552025)
      ·
        refine ⟨10659129471151021647414019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14212172628201362196552025 10659129471151021647414019)
        ·
          refine ⟨15988694206726532471121029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10659129471151021647414019 15988694206726532471121029)
          ·
            refine ⟨2997880163761224838335193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15988694206726532471121029 2997880163761224838335193)
            ·
              refine ⟨2248410122820918628751395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2997880163761224838335193 2248410122820918628751395)
              ·
                refine ⟨3372615184231377943127093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2248410122820918628751395 3372615184231377943127093)
                ·
                  refine ⟨316182673521691682168165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3372615184231377943127093 316182673521691682168165)
                  ·
                    refine ⟨59284251285317190406531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 316182673521691682168165 59284251285317190406531)
                    ·
                      rfl

theorem cell23_346367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 4].length) (baseStart_346367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346367 prefixEnd_346367 := by exact prefixLift 346367
  have htrace : WordTrace (prefixWord ++ tailWord_346367) baseStart_346367 baseEnd_346367 := by
    simpa [prefixWord, tailWord_346367, baseEnd_346367] using wordTrace_append hprefix tailTrace_346367
  have hstable : (prefixWord ++ tailWord_346367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346367).length < 2 ^ (prefixWord ++ tailWord_346367).sum := by decide
  have hdescent : baseEnd_346367 < baseStart_346367 := by decide
  rcases family_descends (prefixWord ++ tailWord_346367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346424 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 5, 1, 3]
def baseStart_346424 : Nat := 118140960795 + 346424 * 2 ^ 59
def prefixEnd_346424 : Nat := 4983230072969 + 3 ^ 40 * 346424 * 2
def baseEnd_346424 : Nat := 177882022253257848206831

theorem tailTrace_346424 : CollatzResearch.WordTrace tailWord_346424 prefixEnd_346424 177882022253257848206831 := by
  unfold tailWord_346424
  simp only [CollatzResearch.WordTrace]
  refine ⟨6317560648486243676991163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8423414197981658235988217 6317560648486243676991163)
  ·
    refine ⟨9476340972729365515486745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6317560648486243676991163 9476340972729365515486745)
    ·
      refine ⟨7107255729547024136615059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9476340972729365515486745 7107255729547024136615059)
      ·
        refine ⟨10660883594320536204922589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7107255729547024136615059 10660883594320536204922589)
        ·
          refine ⟨3997831347870201076845971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10660883594320536204922589 3997831347870201076845971)
          ·
            refine ⟨5996747021805301615268957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3997831347870201076845971 5996747021805301615268957)
            ·
              refine ⟨2248780133176988105725859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5996747021805301615268957 2248780133176988105725859)
              ·
                refine ⟨3373170199765482158588789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2248780133176988105725859 3373170199765482158588789)
                ·
                  refine ⟨316234706228013952367699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3373170199765482158588789 316234706228013952367699)
                  ·
                    refine ⟨474352059342020928551549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 316234706228013952367699 474352059342020928551549)
                    ·
                      refine ⟨177882022253257848206831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 474352059342020928551549 177882022253257848206831)
                      ·
                        rfl

theorem cell23_346424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 5, 1, 3].length) (baseStart_346424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346424 prefixEnd_346424 := by exact prefixLift 346424
  have htrace : WordTrace (prefixWord ++ tailWord_346424) baseStart_346424 baseEnd_346424 := by
    simpa [prefixWord, tailWord_346424, baseEnd_346424] using wordTrace_append hprefix tailTrace_346424
  have hstable : (prefixWord ++ tailWord_346424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346424).length < 2 ^ (prefixWord ++ tailWord_346424).sum := by decide
  have hdescent : baseEnd_346424 < baseStart_346424 := by decide
  rcases family_descends (prefixWord ++ tailWord_346424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346444 : List Nat := [2, 2, 1, 3, 2, 1, 3, 3, 1, 5]
def baseStart_346444 : Nat := 118140960795 + 346444 * 2 ^ 59
def prefixEnd_346444 : Nat := 4983230072969 + 3 ^ 40 * 346444 * 2
def baseEnd_346444 : Nat := 59297430622115923318913

theorem tailTrace_346444 : CollatzResearch.WordTrace tailWord_346444 prefixEnd_346444 59297430622115923318913 := by
  unfold tailWord_346444
  simp only [CollatzResearch.WordTrace]
  refine ⟨6317925378450015384855193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8423900504600020513140257 6317925378450015384855193)
  ·
    refine ⟨4738444033837511538641395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6317925378450015384855193 4738444033837511538641395)
    ·
      refine ⟨7107666050756267307962093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4738444033837511538641395 7107666050756267307962093)
      ·
        refine ⟨2665374769033600240485785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7107666050756267307962093 2665374769033600240485785)
        ·
          refine ⟨1999031076775200180364339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2665374769033600240485785 1999031076775200180364339)
          ·
            refine ⟨2998546615162800270546509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999031076775200180364339 2998546615162800270546509)
            ·
              refine ⟨1124454980686050101454941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2998546615162800270546509 1124454980686050101454941)
              ·
                refine ⟨421670617757268788045603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1124454980686050101454941 421670617757268788045603)
                ·
                  refine ⟨632505926635903182068405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421670617757268788045603 632505926635903182068405)
                  ·
                    refine ⟨59297430622115923318913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 632505926635903182068405 59297430622115923318913)
                    ·
                      rfl

theorem cell23_346444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_346444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346444 prefixEnd_346444 := by exact prefixLift 346444
  have htrace : WordTrace (prefixWord ++ tailWord_346444) baseStart_346444 baseEnd_346444 := by
    simpa [prefixWord, tailWord_346444, baseEnd_346444] using wordTrace_append hprefix tailTrace_346444
  have hstable : (prefixWord ++ tailWord_346444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346444).length < 2 ^ (prefixWord ++ tailWord_346444).sum := by decide
  have hdescent : baseEnd_346444 < baseStart_346444 := by decide
  rcases family_descends (prefixWord ++ tailWord_346444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346447 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 4]
def baseStart_346447 : Nat := 118140960795 + 346447 * 2 ^ 59
def prefixEnd_346447 : Nat := 4983230072969 + 3 ^ 40 * 346447 * 2
def baseEnd_346447 : Nat := 177893832308311258219225

theorem tailTrace_346447 : CollatzResearch.WordTrace tailWord_346447 prefixEnd_346447 177893832308311258219225 := by
  unfold tailWord_346447
  simp only [CollatzResearch.WordTrace]
  refine ⟨12635960175889162282069595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8423973450592774854713063 12635960175889162282069595)
  ·
    refine ⟨18953940263833743423104393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12635960175889162282069595 18953940263833743423104393)
    ·
      refine ⟨14215455197875307567328295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18953940263833743423104393 14215455197875307567328295)
      ·
        refine ⟨21323182796812961350992443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14215455197875307567328295 21323182796812961350992443)
        ·
          refine ⟨31984774195219442026488665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21323182796812961350992443 31984774195219442026488665)
          ·
            refine ⟨23988580646414581519866499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31984774195219442026488665 23988580646414581519866499)
            ·
              refine ⟨35982870969621872279799749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23988580646414581519866499 35982870969621872279799749)
              ·
                refine ⟨6746788306804101052462453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35982870969621872279799749 6746788306804101052462453)
                ·
                  refine ⟨632511403762884473668355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6746788306804101052462453 632511403762884473668355)
                  ·
                    refine ⟨948767105644326710502533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 632511403762884473668355 948767105644326710502533)
                    ·
                      refine ⟨177893832308311258219225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 948767105644326710502533 177893832308311258219225)
                      ·
                        rfl

theorem cell23_346447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 4].length) (baseStart_346447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346447 prefixEnd_346447 := by exact prefixLift 346447
  have htrace : WordTrace (prefixWord ++ tailWord_346447) baseStart_346447 baseEnd_346447 := by
    simpa [prefixWord, tailWord_346447, baseEnd_346447] using wordTrace_append hprefix tailTrace_346447
  have hstable : (prefixWord ++ tailWord_346447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346447).length < 2 ^ (prefixWord ++ tailWord_346447).sum := by decide
  have hdescent : baseEnd_346447 < baseStart_346447 := by decide
  rcases family_descends (prefixWord ++ tailWord_346447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346517 : List Nat := [1, 3, 2, 1, 1, 2, 1, 3, 2, 7]
def baseStart_346517 : Nat := 118140960795 + 346517 * 2 ^ 59
def prefixEnd_346517 : Nat := 4983230072969 + 3 ^ 40 * 346517 * 2
def baseEnd_346517 : Nat := 59309925318041994781301

theorem tailTrace_346517 : CollatzResearch.WordTrace tailWord_346517 prefixEnd_346517 59309925318041994781301 := by
  unfold tailWord_346517
  simp only [CollatzResearch.WordTrace]
  refine ⟨12638513285635564237117805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8425675523757042824745203 12638513285635564237117805)
  ·
    refine ⟨4739442482113336588919177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12638513285635564237117805 4739442482113336588919177)
    ·
      refine ⟨3554581861585002441689383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4739442482113336588919177 3554581861585002441689383)
      ·
        refine ⟨5331872792377503662534075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3554581861585002441689383 5331872792377503662534075)
        ·
          refine ⟨7997809188566255493801113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5331872792377503662534075 7997809188566255493801113)
          ·
            refine ⟨5998356891424691620350835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7997809188566255493801113 5998356891424691620350835)
            ·
              refine ⟨8997535337137037430526253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5998356891424691620350835 8997535337137037430526253)
              ·
                refine ⟨3374075751426389036447345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8997535337137037430526253 3374075751426389036447345)
                ·
                  refine ⟨2530556813569791777335509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3374075751426389036447345 2530556813569791777335509)
                  ·
                    refine ⟨59309925318041994781301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2530556813569791777335509 59309925318041994781301)
                    ·
                      rfl

theorem cell23_346517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 7].length) (baseStart_346517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346517 prefixEnd_346517 := by exact prefixLift 346517
  have htrace : WordTrace (prefixWord ++ tailWord_346517) baseStart_346517 baseEnd_346517 := by
    simpa [prefixWord, tailWord_346517, baseEnd_346517] using wordTrace_append hprefix tailTrace_346517
  have hstable : (prefixWord ++ tailWord_346517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346517).length < 2 ^ (prefixWord ++ tailWord_346517).sum := by decide
  have hdescent : baseEnd_346517 < baseStart_346517 := by decide
  rcases family_descends (prefixWord ++ tailWord_346517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346525 : List Nat := [1, 4, 2, 1, 4, 2, 2, 1, 2, 4]
def baseStart_346525 : Nat := 118140960795 + 346525 * 2 ^ 59
def prefixEnd_346525 : Nat := 4983230072969 + 3 ^ 40 * 346525 * 2
def baseEnd_346525 : Nat := 59311294599787317681289

theorem tailTrace_346525 : CollatzResearch.WordTrace tailWord_346525 prefixEnd_346525 59311294599787317681289 := by
  unfold tailWord_346525
  simp only [CollatzResearch.WordTrace]
  refine ⟨12638805069606581603409029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8425870046404387735606019 12638805069606581603409029)
  ·
    refine ⟨2369775950551234050639193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12638805069606581603409029 2369775950551234050639193)
    ·
      refine ⟨1777331962913425537979395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2369775950551234050639193 1777331962913425537979395)
      ·
        refine ⟨2665997944370138306969093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1777331962913425537979395 2665997944370138306969093)
        ·
          refine ⟨499874614569400932556705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2665997944370138306969093 499874614569400932556705)
          ·
            refine ⟨374905960927050699417529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 499874614569400932556705 374905960927050699417529)
            ·
              refine ⟨281179470695288024563147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374905960927050699417529 281179470695288024563147)
              ·
                refine ⟨421769206042932036844721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281179470695288024563147 421769206042932036844721)
                ·
                  refine ⟨316326904532199027633541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 421769206042932036844721 316326904532199027633541)
                  ·
                    refine ⟨59311294599787317681289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 316326904532199027633541 59311294599787317681289)
                    ·
                      rfl

theorem cell23_346525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 2, 4].length) (baseStart_346525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346525 prefixEnd_346525 := by exact prefixLift 346525
  have htrace : WordTrace (prefixWord ++ tailWord_346525) baseStart_346525 baseEnd_346525 := by
    simpa [prefixWord, tailWord_346525, baseEnd_346525] using wordTrace_append hprefix tailTrace_346525
  have hstable : (prefixWord ++ tailWord_346525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346525).length < 2 ^ (prefixWord ++ tailWord_346525).sum := by decide
  have hdescent : baseEnd_346525 < baseStart_346525 := by decide
  rcases family_descends (prefixWord ++ tailWord_346525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346547 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 6, 6]
def baseStart_346547 : Nat := 118140960795 + 346547 * 2 ^ 59
def prefixEnd_346547 : Nat := 4983230072969 + 3 ^ 40 * 346547 * 2
def baseEnd_346547 : Nat := 59315060124586955656255

theorem tailTrace_346547 : CollatzResearch.WordTrace tailWord_346547 prefixEnd_346547 59315060124586955656255 := by
  unfold tailWord_346547
  simp only [CollatzResearch.WordTrace]
  refine ⟨12639607475526879360709895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8426404983684586240473263 12639607475526879360709895)
  ·
    refine ⟨18959411213290319041064843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12639607475526879360709895 18959411213290319041064843)
    ·
      refine ⟨28439116819935478561597265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18959411213290319041064843 28439116819935478561597265)
      ·
        refine ⟨21329337614951608921197949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28439116819935478561597265 21329337614951608921197949)
        ·
          refine ⟨7998501605606853345449231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21329337614951608921197949 7998501605606853345449231)
          ·
            refine ⟨11997752408410280018173847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7998501605606853345449231 11997752408410280018173847)
            ·
              refine ⟨17996628612615420027260771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11997752408410280018173847 17996628612615420027260771)
              ·
                refine ⟨26994942918923130040891157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17996628612615420027260771 26994942918923130040891157)
                ·
                  refine ⟨1265387949324521720666773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26994942918923130040891157 1265387949324521720666773)
                  ·
                    refine ⟨59315060124586955656255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1265387949324521720666773 59315060124586955656255)
                    ·
                      rfl

theorem cell23_346547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 6].length) (baseStart_346547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346547 prefixEnd_346547 := by exact prefixLift 346547
  have htrace : WordTrace (prefixWord ++ tailWord_346547) baseStart_346547 baseEnd_346547 := by
    simpa [prefixWord, tailWord_346547, baseEnd_346547] using wordTrace_append hprefix tailTrace_346547
  have hstable : (prefixWord ++ tailWord_346547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346547).length < 2 ^ (prefixWord ++ tailWord_346547).sum := by decide
  have hdescent : baseEnd_346547 < baseStart_346547 := by decide
  rcases family_descends (prefixWord ++ tailWord_346547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346558 : List Nat := [4, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2]
def baseStart_346558 : Nat := 118140960795 + 346558 * 2 ^ 59
def prefixEnd_346558 : Nat := 4983230072969 + 3 ^ 40 * 346558 * 2
def baseEnd_346558 : Nat := 177950828660960323931215

theorem tailTrace_346558 : CollatzResearch.WordTrace tailWord_346558 prefixEnd_346558 177950828660960323931215 := by
  unfold tailWord_346558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1580001084810878529920041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8426672452324685492906885 1580001084810878529920041)
  ·
    refine ⟨1185000813608158897440031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1580001084810878529920041 1185000813608158897440031)
    ·
      refine ⟨1777501220412238346160047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1185000813608158897440031 1777501220412238346160047)
      ·
        refine ⟨2666251830618357519240071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1777501220412238346160047 2666251830618357519240071)
        ·
          refine ⟨3999377745927536278860107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2666251830618357519240071 3999377745927536278860107)
          ·
            refine ⟨5999066618891304418290161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3999377745927536278860107 5999066618891304418290161)
            ·
              refine ⟨4499299964168478313717621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5999066618891304418290161 4499299964168478313717621)
              ·
                refine ⟨421809371640794841911027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4499299964168478313717621 421809371640794841911027)
                ·
                  refine ⟨632714057461192262866541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 421809371640794841911027 632714057461192262866541)
                  ·
                    refine ⟨237267771547947098574953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 632714057461192262866541 237267771547947098574953)
                    ·
                      refine ⟨177950828660960323931215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 237267771547947098574953 177950828660960323931215)
                      ·
                        rfl

theorem cell23_346558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_346558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346558 prefixEnd_346558 := by exact prefixLift 346558
  have htrace : WordTrace (prefixWord ++ tailWord_346558) baseStart_346558 baseEnd_346558 := by
    simpa [prefixWord, tailWord_346558, baseEnd_346558] using wordTrace_append hprefix tailTrace_346558
  have hstable : (prefixWord ++ tailWord_346558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346558).length < 2 ^ (prefixWord ++ tailWord_346558).sum := by decide
  have hdescent : baseEnd_346558 < baseStart_346558 := by decide
  rcases family_descends (prefixWord ++ tailWord_346558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346577 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 11]
def baseStart_346577 : Nat := 118140960795 + 346577 * 2 ^ 59
def prefixEnd_346577 : Nat := 4983230072969 + 3 ^ 40 * 346577 * 2
def baseEnd_346577 : Nat := 19773398310377305510403

theorem tailTrace_346577 : CollatzResearch.WordTrace tailWord_346577 prefixEnd_346577 19773398310377305510403 := by
  unfold tailWord_346577
  simp only [CollatzResearch.WordTrace]
  refine ⟨12640701665418194484301985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8427134443612129656201323 12640701665418194484301985)
  ·
    refine ⟨9480526249063645863226489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12640701665418194484301985 9480526249063645863226489)
    ·
      refine ⟨7110394686797734397419867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9480526249063645863226489 7110394686797734397419867)
      ·
        refine ⟨10665592030196601596129801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7110394686797734397419867 10665592030196601596129801)
        ·
          refine ⟨7999194022647451197097351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10665592030196601596129801 7999194022647451197097351)
          ·
            refine ⟨11998791033971176795646027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7999194022647451197097351 11998791033971176795646027)
            ·
              refine ⟨17998186550956765193469041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11998791033971176795646027 17998186550956765193469041)
              ·
                refine ⟨13498639913217573895101781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17998186550956765193469041 13498639913217573895101781)
                ·
                  refine ⟨19773398310377305510403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 13498639913217573895101781 19773398310377305510403)
                  ·
                    rfl

theorem cell23_346577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 11].length) (baseStart_346577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346577 prefixEnd_346577 := by exact prefixLift 346577
  have htrace : WordTrace (prefixWord ++ tailWord_346577) baseStart_346577 baseEnd_346577 := by
    simpa [prefixWord, tailWord_346577, baseEnd_346577] using wordTrace_append hprefix tailTrace_346577
  have hstable : (prefixWord ++ tailWord_346577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346577).length < 2 ^ (prefixWord ++ tailWord_346577).sum := by decide
  have hdescent : baseEnd_346577 < baseStart_346577 := by decide
  rcases family_descends (prefixWord ++ tailWord_346577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346604 : List Nat := [2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 3]
def baseStart_346604 : Nat := 118140960795 + 346604 * 2 ^ 59
def prefixEnd_346604 : Nat := 4983230072969 + 3 ^ 40 * 346604 * 2
def baseEnd_346604 : Nat := 177974448771067143956003

theorem tailTrace_346604 : CollatzResearch.WordTrace tailWord_346604 prefixEnd_346604 177974448771067143956003 := by
  unfold tailWord_346604
  simp only [CollatzResearch.WordTrace]
  refine ⟨6320843218160189047767433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8427790957546918730356577 6320843218160189047767433)
  ·
    refine ⟨4740632413620141785825575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6320843218160189047767433 4740632413620141785825575)
    ·
      refine ⟨7110948620430212678738363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4740632413620141785825575 7110948620430212678738363)
      ·
        refine ⟨10666422930645319018107545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7110948620430212678738363 10666422930645319018107545)
        ·
          refine ⟨7999817197983989263580659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10666422930645319018107545 7999817197983989263580659)
          ·
            refine ⟨11999725796975983895370989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7999817197983989263580659 11999725796975983895370989)
            ·
              refine ⟨4499897173865993960764121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11999725796975983895370989 4499897173865993960764121)
              ·
                refine ⟨3374922880399495470573091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4499897173865993960764121 3374922880399495470573091)
                ·
                  refine ⟨5062384320599243205859637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3374922880399495470573091 5062384320599243205859637)
                  ·
                    refine ⟨474598530056179050549341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5062384320599243205859637 474598530056179050549341)
                    ·
                      refine ⟨177974448771067143956003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 474598530056179050549341 177974448771067143956003)
                      ·
                        rfl

theorem cell23_346604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_346604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346604 prefixEnd_346604 := by exact prefixLift 346604
  have htrace : WordTrace (prefixWord ++ tailWord_346604) baseStart_346604 baseEnd_346604 := by
    simpa [prefixWord, tailWord_346604, baseEnd_346604] using wordTrace_append hprefix tailTrace_346604
  have hstable : (prefixWord ++ tailWord_346604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346604).length < 2 ^ (prefixWord ++ tailWord_346604).sum := by decide
  have hdescent : baseEnd_346604 < baseStart_346604 := by decide
  rcases family_descends (prefixWord ++ tailWord_346604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346611 : List Nat := [1, 1, 1, 2, 2, 2, 6, 3, 5]
def baseStart_346611 : Nat := 118140960795 + 346611 * 2 ^ 59
def prefixEnd_346611 : Nat := 4983230072969 + 3 ^ 40 * 346611 * 2
def baseEnd_346611 : Nat := 19775338126183179618719

theorem tailTrace_346611 : CollatzResearch.WordTrace tailWord_346611 prefixEnd_346611 19775338126183179618719 := by
  unfold tailWord_346611
  simp only [CollatzResearch.WordTrace]
  refine ⟨12641941747295018291039687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8427961164863345527359791 12641941747295018291039687)
  ·
    refine ⟨18962912620942527436559531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12641941747295018291039687 18962912620942527436559531)
    ·
      refine ⟨28444368931413791154839297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18962912620942527436559531 28444368931413791154839297)
      ·
        refine ⟨21333276698560343366129473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28444368931413791154839297 21333276698560343366129473)
        ·
          refine ⟨15999957523920257524597105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21333276698560343366129473 15999957523920257524597105)
          ·
            refine ⟨11999968142940193143447829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15999957523920257524597105 11999968142940193143447829)
            ·
              refine ⟨562498506700321553599117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11999968142940193143447829 562498506700321553599117)
              ·
                refine ⟨210936940012620582599669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 562498506700321553599117 210936940012620582599669)
                ·
                  refine ⟨19775338126183179618719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 210936940012620582599669 19775338126183179618719)
                  ·
                    rfl

theorem cell23_346611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 5].length) (baseStart_346611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346611 prefixEnd_346611 := by exact prefixLift 346611
  have htrace : WordTrace (prefixWord ++ tailWord_346611) baseStart_346611 baseEnd_346611 := by
    simpa [prefixWord, tailWord_346611, baseEnd_346611] using wordTrace_append hprefix tailTrace_346611
  have hstable : (prefixWord ++ tailWord_346611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346611).length < 2 ^ (prefixWord ++ tailWord_346611).sum := by decide
  have hdescent : baseEnd_346611 < baseStart_346611 := by decide
  rcases family_descends (prefixWord ++ tailWord_346611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346628 : List Nat := [2, 3, 2, 3, 1, 1, 2, 4, 5]
def baseStart_346628 : Nat := 118140960795 + 346628 * 2 ^ 59
def prefixEnd_346628 : Nat := 4983230072969 + 3 ^ 40 * 346628 * 2
def baseEnd_346628 : Nat := 19776308034086116672877

theorem tailTrace_346628 : CollatzResearch.WordTrace tailWord_346628 prefixEnd_346628 19776308034086116672877 := by
  unfold tailWord_346628
  simp only [CollatzResearch.WordTrace]
  refine ⟨6321280894116715097204269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8428374525488953462939025 6321280894116715097204269)
  ·
    refine ⟨2370480335293768161451601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6321280894116715097204269 2370480335293768161451601)
    ·
      refine ⟨1777860251470326121088701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2370480335293768161451601 1777860251470326121088701)
      ·
        refine ⟨666697594301372295408263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1777860251470326121088701 666697594301372295408263)
        ·
          refine ⟨1000046391452058443112395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666697594301372295408263 1000046391452058443112395)
          ·
            refine ⟨1500069587178087664668593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000046391452058443112395 1500069587178087664668593)
            ·
              refine ⟨1125052190383565748501445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1500069587178087664668593 1125052190383565748501445)
              ·
                refine ⟨210947285696918577844021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1125052190383565748501445 210947285696918577844021)
                ·
                  refine ⟨19776308034086116672877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 210947285696918577844021 19776308034086116672877)
                  ·
                    rfl

theorem cell23_346628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_346628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346628 prefixEnd_346628 := by exact prefixLift 346628
  have htrace : WordTrace (prefixWord ++ tailWord_346628) baseStart_346628 baseEnd_346628 := by
    simpa [prefixWord, tailWord_346628, baseEnd_346628] using wordTrace_append hprefix tailTrace_346628
  have hstable : (prefixWord ++ tailWord_346628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346628).length < 2 ^ (prefixWord ++ tailWord_346628).sum := by decide
  have hdescent : baseEnd_346628 < baseStart_346628 := by decide
  rcases family_descends (prefixWord ++ tailWord_346628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346634 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_346634 : Nat := 118140960795 + 346634 * 2 ^ 59
def prefixEnd_346634 : Nat := 4983230072969 + 3 ^ 40 * 346634 * 2
def baseEnd_346634 : Nat := 177989853190702026580865

theorem tailTrace_346634 : CollatzResearch.WordTrace tailWord_346634 prefixEnd_346634 177989853190702026580865 := by
  unfold tailWord_346634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160695156552923304781739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8428520417474462146084637 3160695156552923304781739)
  ·
    refine ⟨4741042734829384957172609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3160695156552923304781739 4741042734829384957172609)
    ·
      refine ⟨3555782051122038717879457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4741042734829384957172609 3555782051122038717879457)
      ·
        refine ⟨2666836538341529038409593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3555782051122038717879457 2666836538341529038409593)
        ·
          refine ⟨2000127403756146778807195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2666836538341529038409593 2000127403756146778807195)
          ·
            refine ⟨3000191105634220168210793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2000127403756146778807195 3000191105634220168210793)
            ·
              refine ⟨2250143329225665126158095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3000191105634220168210793 2250143329225665126158095)
              ·
                refine ⟨3375214993838497689237143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250143329225665126158095 3375214993838497689237143)
                ·
                  refine ⟨5062822490757746533855715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375214993838497689237143 5062822490757746533855715)
                  ·
                    refine ⟨7594233736136619800783573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5062822490757746533855715 7594233736136619800783573)
                    ·
                      refine ⟨177989853190702026580865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 7594233736136619800783573 177989853190702026580865)
                      ·
                        rfl

theorem cell23_346634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_346634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346634 prefixEnd_346634 := by exact prefixLift 346634
  have htrace : WordTrace (prefixWord ++ tailWord_346634) baseStart_346634 baseEnd_346634 := by
    simpa [prefixWord, tailWord_346634, baseEnd_346634] using wordTrace_append hprefix tailTrace_346634
  have hstable : (prefixWord ++ tailWord_346634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346634).length < 2 ^ (prefixWord ++ tailWord_346634).sum := by decide
  have hdescent : baseEnd_346634 < baseStart_346634 := by decide
  rcases family_descends (prefixWord ++ tailWord_346634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346661 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 1, 6, 2]
def baseStart_346661 : Nat := 118140960795 + 346661 * 2 ^ 59
def prefixEnd_346661 : Nat := 4983230072969 + 3 ^ 40 * 346661 * 2
def baseEnd_346661 : Nat := 178003717168373420943241

theorem tailTrace_346661 : CollatzResearch.WordTrace tailWord_346661 prefixEnd_346661 178003717168373420943241 := by
  unfold tailWord_346661
  simp only [CollatzResearch.WordTrace]
  refine ⟨12643765397113876830359837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8429176931409251220239891 12643765397113876830359837)
  ·
    refine ⟨4741412023917703811384939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12643765397113876830359837 4741412023917703811384939)
    ·
      refine ⟨7112118035876555717077409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4741412023917703811384939 7112118035876555717077409)
      ·
        refine ⟨5334088526907416787808057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7112118035876555717077409 5334088526907416787808057)
        ·
          refine ⟨4000566395180562590856043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5334088526907416787808057 4000566395180562590856043)
          ·
            refine ⟨6000849592770843886284065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4000566395180562590856043 6000849592770843886284065)
            ·
              refine ⟨4500637194578132914713049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6000849592770843886284065 4500637194578132914713049)
              ·
                refine ⟨3375477895933599686034787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4500637194578132914713049 3375477895933599686034787)
                ·
                  refine ⟨5063216843900399529052181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3375477895933599686034787 5063216843900399529052181)
                  ·
                    refine ⟨237338289557831227924321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5063216843900399529052181 237338289557831227924321)
                    ·
                      refine ⟨178003717168373420943241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 237338289557831227924321 178003717168373420943241)
                      ·
                        rfl

theorem cell23_346661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_346661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346661 prefixEnd_346661 := by exact prefixLift 346661
  have htrace : WordTrace (prefixWord ++ tailWord_346661) baseStart_346661 baseEnd_346661 := by
    simpa [prefixWord, tailWord_346661, baseEnd_346661] using wordTrace_append hprefix tailTrace_346661
  have hstable : (prefixWord ++ tailWord_346661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346661).length < 2 ^ (prefixWord ++ tailWord_346661).sum := by decide
  have hdescent : baseEnd_346661 < baseStart_346661 := by decide
  rcases family_descends (prefixWord ++ tailWord_346661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346674 : List Nat := [3, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6]
def baseStart_346674 : Nat := 118140960795 + 346674 * 2 ^ 59
def prefixEnd_346674 : Nat := 4983230072969 + 3 ^ 40 * 346674 * 2
def baseEnd_346674 : Nat := 178010392416881870080681

theorem tailTrace_346674 : CollatzResearch.WordTrace tailWord_346674 prefixEnd_346674 178010392416881870080681 := by
  unfold tailWord_346674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3161059886516695012645769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8429493030711186700388717 3161059886516695012645769)
  ·
    refine ⟨2370794914887521259484327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3161059886516695012645769 2370794914887521259484327)
    ·
      refine ⟨3556192372331281889226491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2370794914887521259484327 3556192372331281889226491)
      ·
        refine ⟨5334288558496922833839737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3556192372331281889226491 5334288558496922833839737)
        ·
          refine ⟨4000716418872692125379803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5334288558496922833839737 4000716418872692125379803)
          ·
            refine ⟨6001074628309038188069705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4000716418872692125379803 6001074628309038188069705)
            ·
              refine ⟨4500805971231778641052279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6001074628309038188069705 4500805971231778641052279)
              ·
                refine ⟨6751208956847667961578419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4500805971231778641052279 6751208956847667961578419)
                ·
                  refine ⟨10126813435271501942367629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6751208956847667961578419 10126813435271501942367629)
                  ·
                    refine ⟨3797555038226813228387861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10126813435271501942367629 3797555038226813228387861)
                    ·
                      refine ⟨178010392416881870080681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3797555038226813228387861 178010392416881870080681)
                      ·
                        rfl

theorem cell23_346674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_346674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346674 prefixEnd_346674 := by exact prefixLift 346674
  have htrace : WordTrace (prefixWord ++ tailWord_346674) baseStart_346674 baseEnd_346674 := by
    simpa [prefixWord, tailWord_346674, baseEnd_346674] using wordTrace_append hprefix tailTrace_346674
  have hstable : (prefixWord ++ tailWord_346674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346674).length < 2 ^ (prefixWord ++ tailWord_346674).sum := by decide
  have hdescent : baseEnd_346674 < baseStart_346674 := by decide
  rcases family_descends (prefixWord ++ tailWord_346674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346678 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4]
def baseStart_346678 : Nat := 118140960795 + 346678 * 2 ^ 59
def prefixEnd_346678 : Nat := 4983230072969 + 3 ^ 40 * 346678 * 2
def baseEnd_346678 : Nat := 178012446339499854430663

theorem tailTrace_346678 : CollatzResearch.WordTrace tailWord_346678 prefixEnd_346678 178012446339499854430663 := by
  unfold tailWord_346678
  simp only [CollatzResearch.WordTrace]
  refine ⟨790274089878268045858043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8429590292034859155819125 790274089878268045858043)
  ·
    refine ⟨1185411134817402068787065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 790274089878268045858043 1185411134817402068787065)
    ·
      refine ⟨889058351113051551590299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1185411134817402068787065 889058351113051551590299)
      ·
        refine ⟨1333587526669577327385449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 889058351113051551590299 1333587526669577327385449)
        ·
          refine ⟨1000190645002182995539087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1333587526669577327385449 1000190645002182995539087)
          ·
            refine ⟨1500285967503274493308631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000190645002182995539087 1500285967503274493308631)
            ·
              refine ⟨2250428951254911739962947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1500285967503274493308631 2250428951254911739962947)
              ·
                refine ⟨3375643426882367609944421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2250428951254911739962947 3375643426882367609944421)
                ·
                  refine ⟨632933142540443926864579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3375643426882367609944421 632933142540443926864579)
                  ·
                    refine ⟨949399713810665890296869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 632933142540443926864579 949399713810665890296869)
                    ·
                      refine ⟨178012446339499854430663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 949399713810665890296869 178012446339499854430663)
                      ·
                        rfl

theorem cell23_346678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_346678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346678 prefixEnd_346678 := by exact prefixLift 346678
  have htrace : WordTrace (prefixWord ++ tailWord_346678) baseStart_346678 baseEnd_346678 := by
    simpa [prefixWord, tailWord_346678, baseEnd_346678] using wordTrace_append hprefix tailTrace_346678
  have hstable : (prefixWord ++ tailWord_346678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346678).length < 2 ^ (prefixWord ++ tailWord_346678).sum := by decide
  have hdescent : baseEnd_346678 < baseStart_346678 := by decide
  rcases family_descends (prefixWord ++ tailWord_346678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346688 : List Nat := [2, 1, 1, 2, 2, 2, 2, 6, 1, 4]
def baseStart_346688 : Nat := 118140960795 + 346688 * 2 ^ 59
def prefixEnd_346688 : Nat := 4983230072969 + 3 ^ 40 * 346688 * 2
def baseEnd_346688 : Nat := 59339193715348271768539

theorem tailTrace_346688 : CollatzResearch.WordTrace tailWord_346688 prefixEnd_346688 59339193715348271768539 := by
  unfold tailWord_346688
  simp only [CollatzResearch.WordTrace]
  refine ⟨6322375084008030220796359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8429833445344040294395145 6322375084008030220796359)
  ·
    refine ⟨9483562626012045331194539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6322375084008030220796359 9483562626012045331194539)
    ·
      refine ⟨14225343939018067996791809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9483562626012045331194539 14225343939018067996791809)
      ·
        refine ⟨10669007954263550997593857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14225343939018067996791809 10669007954263550997593857)
        ·
          refine ⟨8001755965697663248195393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10669007954263550997593857 8001755965697663248195393)
          ·
            refine ⟨6001316974273247436146545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8001755965697663248195393 6001316974273247436146545)
            ·
              refine ⟨4500987730704935577109909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6001316974273247436146545 4500987730704935577109909)
              ·
                refine ⟨210983799876793855177027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4500987730704935577109909 210983799876793855177027)
                ·
                  refine ⟨316475699815190782765541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210983799876793855177027 316475699815190782765541)
                  ·
                    refine ⟨59339193715348271768539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 316475699815190782765541 59339193715348271768539)
                    ·
                      rfl

theorem cell23_346688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 1, 4].length) (baseStart_346688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346688 prefixEnd_346688 := by exact prefixLift 346688
  have htrace : WordTrace (prefixWord ++ tailWord_346688) baseStart_346688 baseEnd_346688 := by
    simpa [prefixWord, tailWord_346688, baseEnd_346688] using wordTrace_append hprefix tailTrace_346688
  have hstable : (prefixWord ++ tailWord_346688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346688).length < 2 ^ (prefixWord ++ tailWord_346688).sum := by decide
  have hdescent : baseEnd_346688 < baseStart_346688 := by decide
  rcases family_descends (prefixWord ++ tailWord_346688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346761 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 6, 4]
def baseStart_346761 : Nat := 118140960795 + 346761 * 2 ^ 59
def prefixEnd_346761 : Nat := 4983230072969 + 3 ^ 40 * 346761 * 2
def baseEnd_346761 : Nat := 59351688411274343230927

theorem tailTrace_346761 : CollatzResearch.WordTrace tailWord_346761 prefixEnd_346761 59351688411274343230927 := by
  unfold tailWord_346761
  simp only [CollatzResearch.WordTrace]
  refine ⟨12647412696751593909000137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8431608464501062606000091 12647412696751593909000137)
  ·
    refine ⟨9485559522563695431750103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12647412696751593909000137 9485559522563695431750103)
    ·
      refine ⟨14228339283845543147625155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9485559522563695431750103 14228339283845543147625155)
      ·
        refine ⟨21342508925768314721437733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14228339283845543147625155 21342508925768314721437733)
        ·
          refine ⟨4001720423581559010269575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21342508925768314721437733 4001720423581559010269575)
          ·
            refine ⟨6002580635372338515404363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4001720423581559010269575 6002580635372338515404363)
            ·
              refine ⟨9003870953058507773106545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6002580635372338515404363 9003870953058507773106545)
              ·
                refine ⟨6752903214793880829829909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9003870953058507773106545 6752903214793880829829909)
                ·
                  refine ⟨316542338193463163898277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6752903214793880829829909 316542338193463163898277)
                  ·
                    refine ⟨59351688411274343230927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 316542338193463163898277 59351688411274343230927)
                    ·
                      rfl

theorem cell23_346761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 4].length) (baseStart_346761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346761 prefixEnd_346761 := by exact prefixLift 346761
  have htrace : WordTrace (prefixWord ++ tailWord_346761) baseStart_346761 baseEnd_346761 := by
    simpa [prefixWord, tailWord_346761, baseEnd_346761] using wordTrace_append hprefix tailTrace_346761
  have hstable : (prefixWord ++ tailWord_346761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346761).length < 2 ^ (prefixWord ++ tailWord_346761).sum := by decide
  have hdescent : baseEnd_346761 < baseStart_346761 := by decide
  rcases family_descends (prefixWord ++ tailWord_346761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346772 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_346772 : Nat := 118140960795 + 346772 * 2 ^ 59
def prefixEnd_346772 : Nat := 4983230072969 + 3 ^ 40 * 346772 * 2
def baseEnd_346772 : Nat := 178060713521022486655231

theorem tailTrace_346772 : CollatzResearch.WordTrace tailWord_346772 prefixEnd_346772 178060713521022486655231 := by
  unfold tailWord_346772
  simp only [CollatzResearch.WordTrace]
  refine ⟨6323906949855871393825285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8431875933141161858433713 6323906949855871393825285)
  ·
    refine ⟨1185732553097975886342241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6323906949855871393825285 1185732553097975886342241)
    ·
      refine ⟨889299414823481914756681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1185732553097975886342241 889299414823481914756681)
      ·
        refine ⟨666974561117611436067511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 889299414823481914756681 666974561117611436067511)
        ·
          refine ⟨1000461841676417154101267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666974561117611436067511 1000461841676417154101267)
          ·
            refine ⟨1500692762514625731151901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1000461841676417154101267 1500692762514625731151901)
            ·
              refine ⟨562759785942984649181963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1500692762514625731151901 562759785942984649181963)
              ·
                refine ⟨844139678914476973772945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562759785942984649181963 844139678914476973772945)
                ·
                  refine ⟨633104759185857730329709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 844139678914476973772945 633104759185857730329709)
                  ·
                    refine ⟨237414284694696648873641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 633104759185857730329709 237414284694696648873641)
                    ·
                      refine ⟨178060713521022486655231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 237414284694696648873641 178060713521022486655231)
                      ·
                        rfl

theorem cell23_346772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_346772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346772 prefixEnd_346772 := by exact prefixLift 346772
  have htrace : WordTrace (prefixWord ++ tailWord_346772) baseStart_346772 baseEnd_346772 := by
    simpa [prefixWord, tailWord_346772, baseEnd_346772] using wordTrace_append hprefix tailTrace_346772
  have hstable : (prefixWord ++ tailWord_346772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346772).length < 2 ^ (prefixWord ++ tailWord_346772).sum := by decide
  have hdescent : baseEnd_346772 < baseStart_346772 := by decide
  rcases family_descends (prefixWord ++ tailWord_346772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346785 : List Nat := [1, 2, 3, 3, 3, 1, 1, 3, 1, 1, 4]
def baseStart_346785 : Nat := 118140960795 + 346785 * 2 ^ 59
def prefixEnd_346785 : Nat := 4983230072969 + 3 ^ 40 * 346785 * 2
def baseEnd_346785 : Nat := 178067388769530935792671

theorem tailTrace_346785 : CollatzResearch.WordTrace tailWord_346785 prefixEnd_346785 178067388769530935792671 := by
  unfold tailWord_346785
  simp only [CollatzResearch.WordTrace]
  refine ⟨12648288048664646007873809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8432192032443097338582539 12648288048664646007873809)
  ·
    refine ⟨9486216036498484505905357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12648288048664646007873809 9486216036498484505905357)
    ·
      refine ⟨3557331013686931689714509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9486216036498484505905357 3557331013686931689714509)
      ·
        refine ⟨1333999130132599383642941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3557331013686931689714509 1333999130132599383642941)
        ·
          refine ⟨500249673799724768866103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1333999130132599383642941 500249673799724768866103)
          ·
            refine ⟨750374510699587153299155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500249673799724768866103 750374510699587153299155)
            ·
              refine ⟨1125561766049380729948733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750374510699587153299155 1125561766049380729948733)
              ·
                refine ⟨422085662268517773730775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1125561766049380729948733 422085662268517773730775)
                ·
                  refine ⟨633128493402776660596163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 422085662268517773730775 633128493402776660596163)
                  ·
                    refine ⟨949692740104164990894245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 633128493402776660596163 949692740104164990894245)
                    ·
                      refine ⟨178067388769530935792671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 949692740104164990894245 178067388769530935792671)
                      ·
                        rfl

theorem cell23_346785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_346785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346785 prefixEnd_346785 := by exact prefixLift 346785
  have htrace : WordTrace (prefixWord ++ tailWord_346785) baseStart_346785 baseEnd_346785 := by
    simpa [prefixWord, tailWord_346785, baseEnd_346785] using wordTrace_append hprefix tailTrace_346785
  have hstable : (prefixWord ++ tailWord_346785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346785).length < 2 ^ (prefixWord ++ tailWord_346785).sum := by decide
  have hdescent : baseEnd_346785 < baseStart_346785 := by decide
  rcases family_descends (prefixWord ++ tailWord_346785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346871 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 4]
def baseStart_346871 : Nat := 118140960795 + 346871 * 2 ^ 59
def prefixEnd_346871 : Nat := 4983230072969 + 3 ^ 40 * 346871 * 2
def baseEnd_346871 : Nat := 178111548105817599317275

theorem tailTrace_346871 : CollatzResearch.WordTrace tailWord_346871 prefixEnd_346871 178111548105817599317275 := by
  unfold tailWord_346871
  simp only [CollatzResearch.WordTrace]
  refine ⟨12651424726353082695504467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8434283150902055130336311 12651424726353082695504467)
  ·
    refine ⟨18977137089529624043256701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12651424726353082695504467 18977137089529624043256701)
    ·
      refine ⟨7116426408573609016221263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18977137089529624043256701 7116426408573609016221263)
      ·
        refine ⟨10674639612860413524331895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7116426408573609016221263 10674639612860413524331895)
        ·
          refine ⟨16011959419290620286497843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10674639612860413524331895 16011959419290620286497843)
          ·
            refine ⟨24017939128935930429746765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16011959419290620286497843 24017939128935930429746765)
            ·
              refine ⟨9006727173350973911155037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24017939128935930429746765 9006727173350973911155037)
              ·
                refine ⟨3377522690006615216683139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9006727173350973911155037 3377522690006615216683139)
                ·
                  refine ⟨5066284035009922825024709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3377522690006615216683139 5066284035009922825024709)
                  ·
                    refine ⟨949928256564360529692133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5066284035009922825024709 949928256564360529692133)
                    ·
                      refine ⟨178111548105817599317275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 949928256564360529692133 178111548105817599317275)
                      ·
                        rfl

theorem cell23_346871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_346871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346871 prefixEnd_346871 := by exact prefixLift 346871
  have htrace : WordTrace (prefixWord ++ tailWord_346871) baseStart_346871 baseEnd_346871 := by
    simpa [prefixWord, tailWord_346871, baseEnd_346871] using wordTrace_append hprefix tailTrace_346871
  have hstable : (prefixWord ++ tailWord_346871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346871).length < 2 ^ (prefixWord ++ tailWord_346871).sum := by decide
  have hdescent : baseEnd_346871 < baseStart_346871 := by decide
  rcases family_descends (prefixWord ++ tailWord_346871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346881 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 9]
def baseStart_346881 : Nat := 118140960795 + 346881 * 2 ^ 59
def prefixEnd_346881 : Nat := 4983230072969 + 3 ^ 40 * 346881 * 2
def baseEnd_346881 : Nat := 19790742545818062243581

theorem tailTrace_346881 : CollatzResearch.WordTrace tailWord_346881 prefixEnd_346881 19790742545818062243581 := by
  unfold tailWord_346881
  simp only [CollatzResearch.WordTrace]
  refine ⟨12651789456316854403368497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8434526304211236268912331 12651789456316854403368497)
  ·
    refine ⟨9488842092237640802526373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12651789456316854403368497 9488842092237640802526373)
    ·
      refine ⟨1779157892294557650473695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9488842092237640802526373 1779157892294557650473695)
      ·
        refine ⟨2668736838441836475710543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1779157892294557650473695 2668736838441836475710543)
        ·
          refine ⟨4003105257662754713565815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2668736838441836475710543 4003105257662754713565815)
          ·
            refine ⟨6004657886494132070348723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4003105257662754713565815 6004657886494132070348723)
            ·
              refine ⟨9006986829741198105523085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6004657886494132070348723 9006986829741198105523085)
              ·
                refine ⟨3377620061152949289571157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9006986829741198105523085 3377620061152949289571157)
                ·
                  refine ⟨19790742545818062243581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3377620061152949289571157 19790742545818062243581)
                  ·
                    rfl

theorem cell23_346881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 9].length) (baseStart_346881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346881 prefixEnd_346881 := by exact prefixLift 346881
  have htrace : WordTrace (prefixWord ++ tailWord_346881) baseStart_346881 baseEnd_346881 := by
    simpa [prefixWord, tailWord_346881, baseEnd_346881] using wordTrace_append hprefix tailTrace_346881
  have hstable : (prefixWord ++ tailWord_346881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346881).length < 2 ^ (prefixWord ++ tailWord_346881).sum := by decide
  have hdescent : baseEnd_346881 < baseStart_346881 := by decide
  rcases family_descends (prefixWord ++ tailWord_346881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346922 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_346922 : Nat := 118140960795 + 346922 * 2 ^ 59
def prefixEnd_346922 : Nat := 4983230072969 + 3 ^ 40 * 346922 * 2
def baseEnd_346922 : Nat := 178137735619196899779541

theorem tailTrace_346922 : CollatzResearch.WordTrace tailWord_346922 prefixEnd_346922 178137735619196899779541 := by
  unfold tailWord_346922
  simp only [CollatzResearch.WordTrace]
  refine ⟨3163321212292079601402755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8435523232778878937074013 3163321212292079601402755)
  ·
    refine ⟨4744981818438119402104133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3163321212292079601402755 4744981818438119402104133)
    ·
      refine ⟨889684090957147387894525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4744981818438119402104133 889684090957147387894525)
      ·
        refine ⟨333631534108930270460447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 889684090957147387894525 333631534108930270460447)
        ·
          refine ⟨500447301163395405690671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333631534108930270460447 500447301163395405690671)
          ·
            refine ⟨750670951745093108536007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500447301163395405690671 750670951745093108536007)
            ·
              refine ⟨1126006427617639662804011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750670951745093108536007 1126006427617639662804011)
              ·
                refine ⟨1689009641426459494206017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126006427617639662804011 1689009641426459494206017)
                ·
                  refine ⟨1266757231069844620654513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1689009641426459494206017 1266757231069844620654513)
                  ·
                    refine ⟨950067923302383465490885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1266757231069844620654513 950067923302383465490885)
                    ·
                      refine ⟨178137735619196899779541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 950067923302383465490885 178137735619196899779541)
                      ·
                        rfl

theorem cell23_346922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_346922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346922 prefixEnd_346922 := by exact prefixLift 346922
  have htrace : WordTrace (prefixWord ++ tailWord_346922) baseStart_346922 baseEnd_346922 := by
    simpa [prefixWord, tailWord_346922, baseEnd_346922] using wordTrace_append hprefix tailTrace_346922
  have hstable : (prefixWord ++ tailWord_346922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346922).length < 2 ^ (prefixWord ++ tailWord_346922).sum := by decide
  have hdescent : baseEnd_346922 < baseStart_346922 := by decide
  rcases family_descends (prefixWord ++ tailWord_346922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346965 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 4, 4, 2]
def baseStart_346965 : Nat := 118140960795 + 346965 * 2 ^ 59
def prefixEnd_346965 : Nat := 4983230072969 + 3 ^ 40 * 346965 * 2
def baseEnd_346965 : Nat := 178159815287340231541843

theorem tailTrace_346965 : CollatzResearch.WordTrace tailWord_346965 prefixEnd_346965 178159815287340231541843 := by
  unfold tailWord_346965
  simp only [CollatzResearch.WordTrace]
  refine ⟨12654853188012536749426349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8436568792008357832950899 12654853188012536749426349)
  ·
    refine ⟨4745569945504701281034881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12654853188012536749426349 4745569945504701281034881)
    ·
      refine ⟨3559177459128525960776161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4745569945504701281034881 3559177459128525960776161)
      ·
        refine ⟨2669383094346394470582121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3559177459128525960776161 2669383094346394470582121)
        ·
          refine ⟨2002037320759795852936591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2669383094346394470582121 2002037320759795852936591)
          ·
            refine ⟨3003055981139693779404887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2002037320759795852936591 3003055981139693779404887)
            ·
              refine ⟨4504583971709540669107331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3003055981139693779404887 4504583971709540669107331)
              ·
                refine ⟨6756875957564311003660997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4504583971709540669107331 6756875957564311003660997)
                ·
                  refine ⟨1266914242043308313186437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6756875957564311003660997 1266914242043308313186437)
                  ·
                    refine ⟨237546420383120308722457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1266914242043308313186437 237546420383120308722457)
                    ·
                      refine ⟨178159815287340231541843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 237546420383120308722457 178159815287340231541843)
                      ·
                        rfl

theorem cell23_346965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_346965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346965 prefixEnd_346965 := by exact prefixLift 346965
  have htrace : WordTrace (prefixWord ++ tailWord_346965) baseStart_346965 baseEnd_346965 := by
    simpa [prefixWord, tailWord_346965, baseEnd_346965] using wordTrace_append hprefix tailTrace_346965
  have hstable : (prefixWord ++ tailWord_346965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346965).length < 2 ^ (prefixWord ++ tailWord_346965).sum := by decide
  have hdescent : baseEnd_346965 < baseStart_346965 := by decide
  rcases family_descends (prefixWord ++ tailWord_346965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346975 : List Nat := [1, 1, 2, 3, 1, 3, 4, 1, 3, 4]
def baseStart_346975 : Nat := 118140960795 + 346975 * 2 ^ 59
def prefixEnd_346975 : Nat := 4983230072969 + 3 ^ 40 * 346975 * 2
def baseEnd_346975 : Nat := 59388316697961730805599

theorem tailTrace_346975 : CollatzResearch.WordTrace tailWord_346975 prefixEnd_346975 59388316697961730805599 := by
  unfold tailWord_346975
  simp only [CollatzResearch.WordTrace]
  refine ⟨12655217917976308457290379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8436811945317538971526919 12655217917976308457290379)
  ·
    refine ⟨18982826876964462685935569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12655217917976308457290379 18982826876964462685935569)
    ·
      refine ⟨14237120157723347014451677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18982826876964462685935569 14237120157723347014451677)
      ·
        refine ⟨5338920059146255130419379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14237120157723347014451677 5338920059146255130419379)
        ·
          refine ⟨8008380088719382695629069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5338920059146255130419379 8008380088719382695629069)
          ·
            refine ⟨3003142533269768510860901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8008380088719382695629069 3003142533269768510860901)
            ·
              refine ⟨563089224988081595786419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3003142533269768510860901 563089224988081595786419)
              ·
                refine ⟨844633837482122393679629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563089224988081595786419 844633837482122393679629)
                ·
                  refine ⟨316737689055795897629861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844633837482122393679629 316737689055795897629861)
                  ·
                    refine ⟨59388316697961730805599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 316737689055795897629861 59388316697961730805599)
                    ·
                      rfl

theorem cell23_346975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 4].length) (baseStart_346975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_346975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_346975 prefixEnd_346975 := by exact prefixLift 346975
  have htrace : WordTrace (prefixWord ++ tailWord_346975) baseStart_346975 baseEnd_346975 := by
    simpa [prefixWord, tailWord_346975, baseEnd_346975] using wordTrace_append hprefix tailTrace_346975
  have hstable : (prefixWord ++ tailWord_346975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346975).length < 2 ^ (prefixWord ++ tailWord_346975).sum := by decide
  have hdescent : baseEnd_346975 < baseStart_346975 := by decide
  rcases family_descends (prefixWord ++ tailWord_346975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347026 : List Nat := [3, 2, 3, 2, 3, 1, 1, 1, 3, 4]
def baseStart_347026 : Nat := 118140960795 + 347026 * 2 ^ 59
def prefixEnd_347026 : Nat := 4983230072969 + 3 ^ 40 * 347026 * 2
def baseEnd_347026 : Nat := 59397045869088164293021

theorem tailTrace_347026 : CollatzResearch.WordTrace tailWord_347026 prefixEnd_347026 59397045869088164293021 := by
  unfold tailWord_347026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3164269510197886041849233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8438052027194362778264621 3164269510197886041849233)
  ·
    refine ⟨2373202132648414531386925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3164269510197886041849233 2373202132648414531386925)
    ·
      refine ⟨889950799743155449270097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2373202132648414531386925 889950799743155449270097)
      ·
        refine ⟨667463099807366586952573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 889950799743155449270097 667463099807366586952573)
        ·
          refine ⟨250298662427762470107215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 667463099807366586952573 250298662427762470107215)
          ·
            refine ⟨375447993641643705160823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250298662427762470107215 375447993641643705160823)
            ·
              refine ⟨563171990462465557741235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375447993641643705160823 563171990462465557741235)
              ·
                refine ⟨844757985693698336611853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563171990462465557741235 844757985693698336611853)
                ·
                  refine ⟨316784244635136876229445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 844757985693698336611853 316784244635136876229445)
                  ·
                    refine ⟨59397045869088164293021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 316784244635136876229445 59397045869088164293021)
                    ·
                      rfl

theorem cell23_347026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_347026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347026 prefixEnd_347026 := by exact prefixLift 347026
  have htrace : WordTrace (prefixWord ++ tailWord_347026) baseStart_347026 baseEnd_347026 := by
    simpa [prefixWord, tailWord_347026, baseEnd_347026] using wordTrace_append hprefix tailTrace_347026
  have hstable : (prefixWord ++ tailWord_347026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347026).length < 2 ^ (prefixWord ++ tailWord_347026).sum := by decide
  have hdescent : baseEnd_347026 < baseStart_347026 := by decide
  rcases family_descends (prefixWord ++ tailWord_347026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347055 : List Nat := [1, 1, 2, 1, 2, 2, 2, 6, 1, 1, 4]
def baseStart_347055 : Nat := 118140960795 + 347055 * 2 ^ 59
def prefixEnd_347055 : Nat := 4983230072969 + 3 ^ 40 * 347055 * 2
def baseEnd_347055 : Nat := 178206028546244879416429

theorem tailTrace_347055 : CollatzResearch.WordTrace tailWord_347055 prefixEnd_347055 178206028546244879416429 := by
  unfold tailWord_347055
  simp only [CollatzResearch.WordTrace]
  refine ⟨12658135757686482120202619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8438757171790988080135079 12658135757686482120202619)
  ·
    refine ⟨18987203636529723180303929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12658135757686482120202619 18987203636529723180303929)
    ·
      refine ⟨14240402727397292385227947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18987203636529723180303929 14240402727397292385227947)
      ·
        refine ⟨21360604091095938577841921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14240402727397292385227947 21360604091095938577841921)
        ·
          refine ⟨16020453068321953933381441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21360604091095938577841921 16020453068321953933381441)
          ·
            refine ⟨12015339801241465450036081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16020453068321953933381441 12015339801241465450036081)
            ·
              refine ⟨9011504850931099087527061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12015339801241465450036081 9011504850931099087527061)
              ·
                refine ⟨422414289887395269727831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9011504850931099087527061 422414289887395269727831)
                ·
                  refine ⟨633621434831092904591747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 422414289887395269727831 633621434831092904591747)
                  ·
                    refine ⟨950432152246639356887621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 633621434831092904591747 950432152246639356887621)
                    ·
                      refine ⟨178206028546244879416429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 950432152246639356887621 178206028546244879416429)
                      ·
                        rfl

theorem cell23_347055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 1, 4].length) (baseStart_347055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347055 prefixEnd_347055 := by exact prefixLift 347055
  have htrace : WordTrace (prefixWord ++ tailWord_347055) baseStart_347055 baseEnd_347055 := by
    simpa [prefixWord, tailWord_347055, baseEnd_347055] using wordTrace_append hprefix tailTrace_347055
  have hstable : (prefixWord ++ tailWord_347055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347055).length < 2 ^ (prefixWord ++ tailWord_347055).sum := by decide
  have hdescent : baseEnd_347055 < baseStart_347055 := by decide
  rcases family_descends (prefixWord ++ tailWord_347055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347058 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_347058 : Nat := 118140960795 + 347058 * 2 ^ 59
def prefixEnd_347058 : Nat := 4983230072969 + 3 ^ 40 * 347058 * 2
def baseEnd_347058 : Nat := 178207568988208367678915

theorem tailTrace_347058 : CollatzResearch.WordTrace tailWord_347058 prefixEnd_347058 178207568988208367678915 := by
  unfold tailWord_347058
  simp only [CollatzResearch.WordTrace]
  refine ⟨3164561294168903408140457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8438830117783742421707885 3164561294168903408140457)
  ·
    refine ⟨2373420970626677556105343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3164561294168903408140457 2373420970626677556105343)
    ·
      refine ⟨3560131455940016334158015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2373420970626677556105343 3560131455940016334158015)
      ·
        refine ⟨5340197183910024501237023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3560131455940016334158015 5340197183910024501237023)
        ·
          refine ⟨8010295775865036751855535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5340197183910024501237023 8010295775865036751855535)
          ·
            refine ⟨12015443663797555127783303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8010295775865036751855535 12015443663797555127783303)
            ·
              refine ⟨18023165495696332691674955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12015443663797555127783303 18023165495696332691674955)
              ·
                refine ⟨27034748243544499037512433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18023165495696332691674955 27034748243544499037512433)
                ·
                  refine ⟨20276061182658374278134325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27034748243544499037512433 20276061182658374278134325)
                  ·
                    refine ⟨1900880735874222588575093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20276061182658374278134325 1900880735874222588575093)
                    ·
                      refine ⟨178207568988208367678915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1900880735874222588575093 178207568988208367678915)
                      ·
                        rfl

theorem cell23_347058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_347058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347058 prefixEnd_347058 := by exact prefixLift 347058
  have htrace : WordTrace (prefixWord ++ tailWord_347058) baseStart_347058 baseEnd_347058 := by
    simpa [prefixWord, tailWord_347058, baseEnd_347058] using wordTrace_append hprefix tailTrace_347058
  have hstable : (prefixWord ++ tailWord_347058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347058).length < 2 ^ (prefixWord ++ tailWord_347058).sum := by decide
  have hdescent : baseEnd_347058 < baseStart_347058 := by decide
  rcases family_descends (prefixWord ++ tailWord_347058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347065 : List Nat := [1, 2, 1, 4, 2, 3, 1, 2, 1, 6]
def baseStart_347065 : Nat := 118140960795 + 347065 * 2 ^ 59
def prefixEnd_347065 : Nat := 4983230072969 + 3 ^ 40 * 347065 * 2
def baseEnd_347065 : Nat := 59403721117596613430461

theorem tailTrace_347065 : CollatzResearch.WordTrace tailWord_347065 prefixEnd_347065 59403721117596613430461 := by
  unfold tailWord_347065
  simp only [CollatzResearch.WordTrace]
  refine ⟨12658500487650253828066649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8439000325100169218711099 12658500487650253828066649)
  ·
    refine ⟨9493875365737690371049987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12658500487650253828066649 9493875365737690371049987)
    ·
      refine ⟨14240813048606535556574981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9493875365737690371049987 14240813048606535556574981)
      ·
        refine ⟨2670152446613725416857809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14240813048606535556574981 2670152446613725416857809)
        ·
          refine ⟨2002614334960294062643357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2670152446613725416857809 2002614334960294062643357)
          ·
            refine ⟨750980375610110273491259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2002614334960294062643357 750980375610110273491259)
            ·
              refine ⟨1126470563415165410236889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750980375610110273491259 1126470563415165410236889)
              ·
                refine ⟨844852922561374057677667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1126470563415165410236889 844852922561374057677667)
                ·
                  refine ⟨1267279383842061086516501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 844852922561374057677667 1267279383842061086516501)
                  ·
                    refine ⟨59403721117596613430461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1267279383842061086516501 59403721117596613430461)
                    ·
                      rfl

theorem cell23_347065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 6].length) (baseStart_347065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347065 prefixEnd_347065 := by exact prefixLift 347065
  have htrace : WordTrace (prefixWord ++ tailWord_347065) baseStart_347065 baseEnd_347065 := by
    simpa [prefixWord, tailWord_347065, baseEnd_347065] using wordTrace_append hprefix tailTrace_347065
  have hstable : (prefixWord ++ tailWord_347065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347065).length < 2 ^ (prefixWord ++ tailWord_347065).sum := by decide
  have hdescent : baseEnd_347065 < baseStart_347065 := by decide
  rcases family_descends (prefixWord ++ tailWord_347065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347069 : List Nat := [1, 4, 1, 2, 4, 1, 3, 1, 1, 5]
def baseStart_347069 : Nat := 118140960795 + 347069 * 2 ^ 59
def prefixEnd_347069 : Nat := 4983230072969 + 3 ^ 40 * 347069 * 2
def baseEnd_347069 : Nat := 59404405758469274880455

theorem tailTrace_347069 : CollatzResearch.WordTrace tailWord_347069 prefixEnd_347069 59404405758469274880455 := by
  unfold tailWord_347069
  simp only [CollatzResearch.WordTrace]
  refine ⟨12658646379635762511212261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8439097586423841674141507 12658646379635762511212261)
  ·
    refine ⟨2373496196181705470852299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12658646379635762511212261 2373496196181705470852299)
    ·
      refine ⟨3560244294272558206278449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2373496196181705470852299 3560244294272558206278449)
      ·
        refine ⟨2670183220704418654708837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3560244294272558206278449 2670183220704418654708837)
        ·
          refine ⟨500659353882078497757907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2670183220704418654708837 500659353882078497757907)
          ·
            refine ⟨750989030823117746636861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500659353882078497757907 750989030823117746636861)
            ·
              refine ⟨281620886558669154988823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 750989030823117746636861 281620886558669154988823)
              ·
                refine ⟨422431329838003732483235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281620886558669154988823 422431329838003732483235)
                ·
                  refine ⟨633646994757005598724853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 422431329838003732483235 633646994757005598724853)
                  ·
                    refine ⟨59404405758469274880455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 633646994757005598724853 59404405758469274880455)
                    ·
                      rfl

theorem cell23_347069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 1, 5].length) (baseStart_347069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347069 prefixEnd_347069 := by exact prefixLift 347069
  have htrace : WordTrace (prefixWord ++ tailWord_347069) baseStart_347069 baseEnd_347069 := by
    simpa [prefixWord, tailWord_347069, baseEnd_347069] using wordTrace_append hprefix tailTrace_347069
  have hstable : (prefixWord ++ tailWord_347069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347069).length < 2 ^ (prefixWord ++ tailWord_347069).sum := by decide
  have hdescent : baseEnd_347069 < baseStart_347069 := by decide
  rcases family_descends (prefixWord ++ tailWord_347069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347092 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 3, 2, 3]
def baseStart_347092 : Nat := 118140960795 + 347092 * 2 ^ 59
def prefixEnd_347092 : Nat := 4983230072969 + 3 ^ 40 * 347092 * 2
def baseEnd_347092 : Nat := 178225027330461234653759

theorem tailTrace_347092 : CollatzResearch.WordTrace tailWord_347092 prefixEnd_347092 178225027330461234653759 := by
  unfold tailWord_347092
  simp only [CollatzResearch.WordTrace]
  refine ⟨6329742629276218719649765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8439656839034958292866353 6329742629276218719649765)
  ·
    refine ⟨1186826742989291009934331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6329742629276218719649765 1186826742989291009934331)
    ·
      refine ⟨1780240114483936514901497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1186826742989291009934331 1780240114483936514901497)
      ·
        refine ⟨1335180085862952386176123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1780240114483936514901497 1335180085862952386176123)
        ·
          refine ⟨2002770128794428579264185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1335180085862952386176123 2002770128794428579264185)
          ·
            refine ⟨1502077596595821434448139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2002770128794428579264185 1502077596595821434448139)
            ·
              refine ⟨2253116394893732151672209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502077596595821434448139 2253116394893732151672209)
              ·
                refine ⟨1689837296170299113754157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2253116394893732151672209 1689837296170299113754157)
                ·
                  refine ⟨633688986063862167657809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1689837296170299113754157 633688986063862167657809)
                  ·
                    refine ⟨475266739547896625743357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 633688986063862167657809 475266739547896625743357)
                    ·
                      refine ⟨178225027330461234653759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 475266739547896625743357 178225027330461234653759)
                      ·
                        rfl

theorem cell23_347092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_347092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347092 prefixEnd_347092 := by exact prefixLift 347092
  have htrace : WordTrace (prefixWord ++ tailWord_347092) baseStart_347092 baseEnd_347092 := by
    simpa [prefixWord, tailWord_347092, baseEnd_347092] using wordTrace_append hprefix tailTrace_347092
  have hstable : (prefixWord ++ tailWord_347092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347092).length < 2 ^ (prefixWord ++ tailWord_347092).sum := by decide
  have hdescent : baseEnd_347092 < baseStart_347092 := by decide
  rcases family_descends (prefixWord ++ tailWord_347092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347106 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 5, 2, 2]
def baseStart_347106 : Nat := 118140960795 + 347106 * 2 ^ 59
def prefixEnd_347106 : Nat := 4983230072969 + 3 ^ 40 * 347106 * 2
def baseEnd_347106 : Nat := 178232216059624179878695

theorem tailTrace_347106 : CollatzResearch.WordTrace tailWord_347106 prefixEnd_347106 178232216059624179878695 := by
  unfold tailWord_347106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3164998970125429457577293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8439997253667811886872781 3164998970125429457577293)
  ·
    refine ⟨1186874613797036046591485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3164998970125429457577293 1186874613797036046591485)
    ·
      refine ⟨445077980173888517471807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1186874613797036046591485 445077980173888517471807)
      ·
        refine ⟨667616970260832776207711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445077980173888517471807 667616970260832776207711)
        ·
          refine ⟨1001425455391249164311567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667616970260832776207711 1001425455391249164311567)
          ·
            refine ⟨1502138183086873746467351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001425455391249164311567 1502138183086873746467351)
            ·
              refine ⟨2253207274630310619701027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502138183086873746467351 2253207274630310619701027)
              ·
                refine ⟨3379810911945465929551541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2253207274630310619701027 3379810911945465929551541)
                ·
                  refine ⟨316857272994887430895457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3379810911945465929551541 316857272994887430895457)
                  ·
                    refine ⟨237642954746165573171593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 316857272994887430895457 237642954746165573171593)
                    ·
                      refine ⟨178232216059624179878695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 237642954746165573171593 178232216059624179878695)
                      ·
                        rfl

theorem cell23_347106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_347106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347106 prefixEnd_347106 := by exact prefixLift 347106
  have htrace : WordTrace (prefixWord ++ tailWord_347106) baseStart_347106 baseEnd_347106 := by
    simpa [prefixWord, tailWord_347106, baseEnd_347106] using wordTrace_append hprefix tailTrace_347106
  have hstable : (prefixWord ++ tailWord_347106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347106).length < 2 ^ (prefixWord ++ tailWord_347106).sum := by decide
  have hdescent : baseEnd_347106 < baseStart_347106 := by decide
  rcases family_descends (prefixWord ++ tailWord_347106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347126 : List Nat := [5, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3]
def baseStart_347126 : Nat := 118140960795 + 347126 * 2 ^ 59
def prefixEnd_347126 : Nat := 4983230072969 + 3 ^ 40 * 347126 * 2
def baseEnd_347126 : Nat := 178242485672714101628603

theorem tailTrace_347126 : CollatzResearch.WordTrace tailWord_347126 prefixEnd_347126 178242485672714101628603 := by
  unfold tailWord_347126
  simp only [CollatzResearch.WordTrace]
  refine ⟨791295333776828827877327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8440483560286174164024821 791295333776828827877327)
  ·
    refine ⟨1186943000665243241815991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 791295333776828827877327 1186943000665243241815991)
    ·
      refine ⟨1780414500997864862723987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1186943000665243241815991 1780414500997864862723987)
      ·
        refine ⟨2670621751496797294085981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1780414500997864862723987 2670621751496797294085981)
        ·
          refine ⟨1001483156811298985282243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2670621751496797294085981 1001483156811298985282243)
          ·
            refine ⟨1502224735216948477923365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001483156811298985282243 1502224735216948477923365)
            ·
              refine ⟨281667137853177839610631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1502224735216948477923365 281667137853177839610631)
              ·
                refine ⟨422500706779766759415947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281667137853177839610631 422500706779766759415947)
                ·
                  refine ⟨633751060169650139123921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 422500706779766759415947 633751060169650139123921)
                  ·
                    refine ⟨475313295127237604342941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 633751060169650139123921 475313295127237604342941)
                    ·
                      refine ⟨178242485672714101628603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 475313295127237604342941 178242485672714101628603)
                      ·
                        rfl

theorem cell23_347126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_347126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347126 prefixEnd_347126 := by exact prefixLift 347126
  have htrace : WordTrace (prefixWord ++ tailWord_347126) baseStart_347126 baseEnd_347126 := by
    simpa [prefixWord, tailWord_347126, baseEnd_347126] using wordTrace_append hprefix tailTrace_347126
  have hstable : (prefixWord ++ tailWord_347126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347126).length < 2 ^ (prefixWord ++ tailWord_347126).sum := by decide
  have hdescent : baseEnd_347126 < baseStart_347126 := by decide
  rcases family_descends (prefixWord ++ tailWord_347126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347182 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_347182 : Nat := 118140960795 + 347182 * 2 ^ 59
def prefixEnd_347182 : Nat := 4983230072969 + 3 ^ 40 * 347182 * 2
def baseEnd_347182 : Nat := 178271240589365882528345

theorem tailTrace_347182 : CollatzResearch.WordTrace tailWord_347182 prefixEnd_347182 178271240589365882528345 := by
  unfold tailWord_347182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582845978528297851259475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8441845218817588540050533 1582845978528297851259475)
  ·
    refine ⟨2374268967792446776889213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1582845978528297851259475 2374268967792446776889213)
    ·
      refine ⟨890350862922167541333455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2374268967792446776889213 890350862922167541333455)
      ·
        refine ⟨1335526294383251312000183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 890350862922167541333455 1335526294383251312000183)
        ·
          refine ⟨2003289441574876968000275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1335526294383251312000183 2003289441574876968000275)
          ·
            refine ⟨3004934162362315452000413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003289441574876968000275 3004934162362315452000413)
            ·
              refine ⟨1126850310885868294500155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3004934162362315452000413 1126850310885868294500155)
              ·
                refine ⟨1690275466328802441750233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126850310885868294500155 1690275466328802441750233)
                ·
                  refine ⟨1267706599746601831312675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1690275466328802441750233 1267706599746601831312675)
                  ·
                    refine ⟨1901559899619902746969013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1267706599746601831312675 1901559899619902746969013)
                    ·
                      refine ⟨178271240589365882528345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1901559899619902746969013 178271240589365882528345)
                      ·
                        rfl

theorem cell23_347182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_347182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347182 prefixEnd_347182 := by exact prefixLift 347182
  have htrace : WordTrace (prefixWord ++ tailWord_347182) baseStart_347182 baseEnd_347182 := by
    simpa [prefixWord, tailWord_347182, baseEnd_347182] using wordTrace_append hprefix tailTrace_347182
  have hstable : (prefixWord ++ tailWord_347182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347182).length < 2 ^ (prefixWord ++ tailWord_347182).sum := by decide
  have hdescent : baseEnd_347182 < baseStart_347182 := by decide
  rcases family_descends (prefixWord ++ tailWord_347182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347213 : List Nat := [1, 6, 1, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_347213 : Nat := 118140960795 + 347213 * 2 ^ 59
def prefixEnd_347213 : Nat := 4983230072969 + 3 ^ 40 * 347213 * 2
def baseEnd_347213 : Nat := 178287158489655261240703

theorem tailTrace_347213 : CollatzResearch.WordTrace tailWord_347213 prefixEnd_347213 178287158489655261240703 := by
  unfold tailWord_347213
  simp only [CollatzResearch.WordTrace]
  refine ⟨12663898491114075104454293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8442598994076050069636195 12663898491114075104454293)
  ·
    refine ⟨593620241770972270521295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12663898491114075104454293 593620241770972270521295)
    ·
      refine ⟨890430362656458405781943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 593620241770972270521295 890430362656458405781943)
      ·
        refine ⟨1335645543984687608672915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 890430362656458405781943 1335645543984687608672915)
        ·
          refine ⟨2003468315977031413009373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1335645543984687608672915 2003468315977031413009373)
          ·
            refine ⟨751300618491386779878515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2003468315977031413009373 751300618491386779878515)
            ·
              refine ⟨1126950927737080169817773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751300618491386779878515 1126950927737080169817773)
              ·
                refine ⟨422606597901405063681665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1126950927737080169817773 422606597901405063681665)
                ·
                  refine ⟨316954948426053797761249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 422606597901405063681665 316954948426053797761249)
                  ·
                    refine ⟨237716211319540348320937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 316954948426053797761249 237716211319540348320937)
                    ·
                      refine ⟨178287158489655261240703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 237716211319540348320937 178287158489655261240703)
                      ·
                        rfl

theorem cell23_347213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_347213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347213 prefixEnd_347213 := by exact prefixLift 347213
  have htrace : WordTrace (prefixWord ++ tailWord_347213) baseStart_347213 baseEnd_347213 := by
    simpa [prefixWord, tailWord_347213, baseEnd_347213] using wordTrace_append hprefix tailTrace_347213
  have hstable : (prefixWord ++ tailWord_347213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347213).length < 2 ^ (prefixWord ++ tailWord_347213).sum := by decide
  have hdescent : baseEnd_347213 < baseStart_347213 := by decide
  rcases family_descends (prefixWord ++ tailWord_347213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347232 : List Nat := [2, 1, 1, 3, 2, 2, 4, 1, 2, 5]
def baseStart_347232 : Nat := 118140960795 + 347232 * 2 ^ 59
def prefixEnd_347232 : Nat := 4983230072969 + 3 ^ 40 * 347232 * 2
def baseEnd_347232 : Nat := 59432304874030228967705

theorem tailTrace_347232 : CollatzResearch.WordTrace tailWord_347232 prefixEnd_347232 59432304874030228967705 := by
  unfold tailWord_347232
  simp only [CollatzResearch.WordTrace]
  refine ⟨6332295739022620674697975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8443060985363494232930633 6332295739022620674697975)
  ·
    refine ⟨9498443608533931012046963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6332295739022620674697975 9498443608533931012046963)
    ·
      refine ⟨14247665412800896518070445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9498443608533931012046963 14247665412800896518070445)
      ·
        refine ⟨5342874529800336194276417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14247665412800896518070445 5342874529800336194276417)
        ·
          refine ⟨4007155897350252145707313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5342874529800336194276417 4007155897350252145707313)
          ·
            refine ⟨3005366923012689109280485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4007155897350252145707313 3005366923012689109280485)
            ·
              refine ⟨563506298064879207990091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3005366923012689109280485 563506298064879207990091)
              ·
                refine ⟨845259447097318811985137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563506298064879207990091 845259447097318811985137)
                ·
                  refine ⟨633944585322989108988853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 845259447097318811985137 633944585322989108988853)
                  ·
                    refine ⟨59432304874030228967705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 633944585322989108988853 59432304874030228967705)
                    ·
                      rfl

theorem cell23_347232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 1, 2, 5].length) (baseStart_347232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347232 prefixEnd_347232 := by exact prefixLift 347232
  have htrace : WordTrace (prefixWord ++ tailWord_347232) baseStart_347232 baseEnd_347232 := by
    simpa [prefixWord, tailWord_347232, baseEnd_347232] using wordTrace_append hprefix tailTrace_347232
  have hstable : (prefixWord ++ tailWord_347232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347232).length < 2 ^ (prefixWord ++ tailWord_347232).sum := by decide
  have hdescent : baseEnd_347232 < baseStart_347232 := by decide
  rcases family_descends (prefixWord ++ tailWord_347232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347242 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_347242 : Nat := 118140960795 + 347242 * 2 ^ 59
def prefixEnd_347242 : Nat := 4983230072969 + 3 ^ 40 * 347242 * 2
def baseEnd_347242 : Nat := 178302049428635647778069

theorem tailTrace_347242 : CollatzResearch.WordTrace tailWord_347242 prefixEnd_347242 178302049428635647778069 := by
  unfold tailWord_347242
  simp only [CollatzResearch.WordTrace]
  refine ⟨3166239052002253264314995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8443304138672675371506653 3166239052002253264314995)
  ·
    refine ⟨4749358578003379896472493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3166239052002253264314995 4749358578003379896472493)
    ·
      refine ⟨1781009466751267461177185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4749358578003379896472493 1781009466751267461177185)
      ·
        refine ⟨1335757100063450595882889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1781009466751267461177185 1335757100063450595882889)
        ·
          refine ⟨1001817825047587946912167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1335757100063450595882889 1001817825047587946912167)
          ·
            refine ⟨1502726737571381920368251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001817825047587946912167 1502726737571381920368251)
            ·
              refine ⟨2254090106357072880552377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502726737571381920368251 2254090106357072880552377)
              ·
                refine ⟨1690567579767804660414283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2254090106357072880552377 1690567579767804660414283)
                ·
                  refine ⟨2535851369651706990621425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690567579767804660414283 2535851369651706990621425)
                  ·
                    refine ⟨1901888527238780242966069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2535851369651706990621425 1901888527238780242966069)
                    ·
                      refine ⟨178302049428635647778069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1901888527238780242966069 178302049428635647778069)
                      ·
                        rfl

theorem cell23_347242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_347242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347242 prefixEnd_347242 := by exact prefixLift 347242
  have htrace : WordTrace (prefixWord ++ tailWord_347242) baseStart_347242 baseEnd_347242 := by
    simpa [prefixWord, tailWord_347242, baseEnd_347242] using wordTrace_append hprefix tailTrace_347242
  have hstable : (prefixWord ++ tailWord_347242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347242).length < 2 ^ (prefixWord ++ tailWord_347242).sum := by decide
  have hdescent : baseEnd_347242 < baseStart_347242 := by decide
  rcases family_descends (prefixWord ++ tailWord_347242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347255 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 5]
def baseStart_347255 : Nat := 118140960795 + 347255 * 2 ^ 59
def prefixEnd_347255 : Nat := 4983230072969 + 3 ^ 40 * 347255 * 2
def baseEnd_347255 : Nat := 178308724677144096915509

theorem tailTrace_347255 : CollatzResearch.WordTrace tailWord_347255 prefixEnd_347255 178308724677144096915509 := by
  unfold tailWord_347255
  simp only [CollatzResearch.WordTrace]
  refine ⟨12665430356961916277483219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8443620237974610851655479 12665430356961916277483219)
  ·
    refine ⟨18998145535442874416224829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12665430356961916277483219 18998145535442874416224829)
    ·
      refine ⟨7124304575791077906084311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18998145535442874416224829 7124304575791077906084311)
      ·
        refine ⟨10686456863686616859126467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7124304575791077906084311 10686456863686616859126467)
        ·
          refine ⟨16029685295529925288689701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10686456863686616859126467 16029685295529925288689701)
          ·
            refine ⟨3005565992911860991629319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16029685295529925288689701 3005565992911860991629319)
            ·
              refine ⟨4508348989367791487443979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3005565992911860991629319 4508348989367791487443979)
              ·
                refine ⟨6762523484051687231165969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4508348989367791487443979 6762523484051687231165969)
                ·
                  refine ⟨5071892613038765423374477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6762523484051687231165969 5071892613038765423374477)
                  ·
                    refine ⟨1901959729889537033765429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5071892613038765423374477 1901959729889537033765429)
                    ·
                      refine ⟨178308724677144096915509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1901959729889537033765429 178308724677144096915509)
                      ·
                        rfl

theorem cell23_347255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_347255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347255 prefixEnd_347255 := by exact prefixLift 347255
  have htrace : WordTrace (prefixWord ++ tailWord_347255) baseStart_347255 baseEnd_347255 := by
    simpa [prefixWord, tailWord_347255, baseEnd_347255] using wordTrace_append hprefix tailTrace_347255
  have hstable : (prefixWord ++ tailWord_347255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347255).length < 2 ^ (prefixWord ++ tailWord_347255).sum := by decide
  have hdescent : baseEnd_347255 < baseStart_347255 := by decide
  rcases family_descends (prefixWord ++ tailWord_347255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347296 : List Nat := [2, 1, 1, 4, 2, 1, 4, 3, 1, 4]
def baseStart_347296 : Nat := 118140960795 + 347296 * 2 ^ 59
def prefixEnd_347296 : Nat := 4983230072969 + 3 ^ 40 * 347296 * 2
def baseEnd_347296 : Nat := 59443259127992812167607

theorem tailTrace_347296 : CollatzResearch.WordTrace tailWord_347296 prefixEnd_347296 59443259127992812167607 := by
  unfold tailWord_347296
  simp only [CollatzResearch.WordTrace]
  refine ⟨6333462874906690139862871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8444617166542253519817161 6333462874906690139862871)
  ·
    refine ⟨9500194312360035209794307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6333462874906690139862871 9500194312360035209794307)
    ·
      refine ⟨14250291468540052814691461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9500194312360035209794307 14250291468540052814691461)
      ·
        refine ⟨2671929650351259902754649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14250291468540052814691461 2671929650351259902754649)
        ·
          refine ⟨2003947237763444927065987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2671929650351259902754649 2003947237763444927065987)
          ·
            refine ⟨3005920856645167390598981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003947237763444927065987 3005920856645167390598981)
            ·
              refine ⟨563610160620968885737309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3005920856645167390598981 563610160620968885737309)
              ·
                refine ⟨211353810232863332151491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 563610160620968885737309 211353810232863332151491)
                ·
                  refine ⟨317030715349294998227237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211353810232863332151491 317030715349294998227237)
                  ·
                    refine ⟨59443259127992812167607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 317030715349294998227237 59443259127992812167607)
                    ·
                      rfl

theorem cell23_347296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 3, 1, 4].length) (baseStart_347296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347296 prefixEnd_347296 := by exact prefixLift 347296
  have htrace : WordTrace (prefixWord ++ tailWord_347296) baseStart_347296 baseEnd_347296 := by
    simpa [prefixWord, tailWord_347296, baseEnd_347296] using wordTrace_append hprefix tailTrace_347296
  have hstable : (prefixWord ++ tailWord_347296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347296).length < 2 ^ (prefixWord ++ tailWord_347296).sum := by decide
  have hdescent : baseEnd_347296 < baseStart_347296 := by decide
  rcases family_descends (prefixWord ++ tailWord_347296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347309 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 8]
def baseStart_347309 : Nat := 118140960795 + 347309 * 2 ^ 59
def prefixEnd_347309 : Nat := 4983230072969 + 3 ^ 40 * 347309 * 2
def baseEnd_347309 : Nat := 19815161403609653960029

theorem tailTrace_347309 : CollatzResearch.WordTrace tailWord_347309 prefixEnd_347309 19815161403609653960029 := by
  unfold tailWord_347309
  simp only [CollatzResearch.WordTrace]
  refine ⟨12667399898766283499948981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8444933265844188999965987 12667399898766283499948981)
  ·
    refine ⟨1187568740509339078120217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12667399898766283499948981 1187568740509339078120217)
    ·
      refine ⟨890676555382004308590163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1187568740509339078120217 890676555382004308590163)
      ·
        refine ⟨1336014833073006462885245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 890676555382004308590163 1336014833073006462885245)
        ·
          refine ⟨501005562402377423581967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1336014833073006462885245 501005562402377423581967)
          ·
            refine ⟨751508343603566135372951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501005562402377423581967 751508343603566135372951)
            ·
              refine ⟨1127262515405349203059427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751508343603566135372951 1127262515405349203059427)
              ·
                refine ⟨1690893773108023804589141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1127262515405349203059427 1690893773108023804589141)
                ·
                  refine ⟨19815161403609653960029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1690893773108023804589141 19815161403609653960029)
                  ·
                    rfl

theorem cell23_347309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_347309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347309 prefixEnd_347309 := by exact prefixLift 347309
  have htrace : WordTrace (prefixWord ++ tailWord_347309) baseStart_347309 baseEnd_347309 := by
    simpa [prefixWord, tailWord_347309, baseEnd_347309] using wordTrace_append hprefix tailTrace_347309
  have hstable : (prefixWord ++ tailWord_347309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347309).length < 2 ^ (prefixWord ++ tailWord_347309).sum := by decide
  have hdescent : baseEnd_347309 < baseStart_347309 := by decide
  rcases family_descends (prefixWord ++ tailWord_347309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347326 : List Nat := [4, 2, 1, 1, 3, 2, 3, 1, 6]
def baseStart_347326 : Nat := 118140960795 + 347326 * 2 ^ 59
def prefixEnd_347326 : Nat := 4983230072969 + 3 ^ 40 * 347326 * 2
def baseEnd_347326 : Nat := 19816131311512591014187

theorem tailTrace_347326 : CollatzResearch.WordTrace tailWord_347326 prefixEnd_347326 19816131311512591014187 := by
  unfold tailWord_347326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1583502492463086925414729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8445346626469796935545221 1583502492463086925414729)
  ·
    refine ⟨1187626869347315194061047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1583502492463086925414729 1187626869347315194061047)
    ·
      refine ⟨1781440304020972791091571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1187626869347315194061047 1781440304020972791091571)
      ·
        refine ⟨2672160456031459186637357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1781440304020972791091571 2672160456031459186637357)
        ·
          refine ⟨1002060171011797194989009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2672160456031459186637357 1002060171011797194989009)
          ·
            refine ⟨751545128258847896241757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1002060171011797194989009 751545128258847896241757)
            ·
              refine ⟨281829423097067961090659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 751545128258847896241757 281829423097067961090659)
              ·
                refine ⟨422744134645601941635989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281829423097067961090659 422744134645601941635989)
                ·
                  refine ⟨19816131311512591014187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 422744134645601941635989 19816131311512591014187)
                  ·
                    rfl

theorem cell23_347326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_347326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347326 prefixEnd_347326 := by exact prefixLift 347326
  have htrace : WordTrace (prefixWord ++ tailWord_347326) baseStart_347326 baseEnd_347326 := by
    simpa [prefixWord, tailWord_347326, baseEnd_347326] using wordTrace_append hprefix tailTrace_347326
  have hstable : (prefixWord ++ tailWord_347326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347326).length < 2 ^ (prefixWord ++ tailWord_347326).sum := by decide
  have hdescent : baseEnd_347326 < baseStart_347326 := by decide
  rcases family_descends (prefixWord ++ tailWord_347326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347346 : List Nat := [3, 2, 2, 2, 1, 1, 2, 3, 2, 3, 2]
def baseStart_347346 : Nat := 118140960795 + 347346 * 2 ^ 59
def prefixEnd_347346 : Nat := 4983230072969 + 3 ^ 40 * 347346 * 2
def baseEnd_347346 : Nat := 178355451416703240877591

theorem tailTrace_347346 : CollatzResearch.WordTrace tailWord_347346 prefixEnd_347346 178355451416703240877591 := by
  unfold tailWord_347346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3167187349908059704761473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8445832933088159212697261 3167187349908059704761473)
  ·
    refine ⟨2375390512431044778571105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3167187349908059704761473 2375390512431044778571105)
    ·
      refine ⟨1781542884323283583928329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2375390512431044778571105 1781542884323283583928329)
      ·
        refine ⟨1336157163242462687946247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1781542884323283583928329 1336157163242462687946247)
        ·
          refine ⟨2004235744863694031919371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1336157163242462687946247 2004235744863694031919371)
          ·
            refine ⟨3006353617295541047879057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2004235744863694031919371 3006353617295541047879057)
            ·
              refine ⟨2254765212971655785909293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3006353617295541047879057 2254765212971655785909293)
              ·
                refine ⟨845536954864370919715985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2254765212971655785909293 845536954864370919715985)
                ·
                  refine ⟨634152716148278189786989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 845536954864370919715985 634152716148278189786989)
                  ·
                    refine ⟨237807268555604321170121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 634152716148278189786989 237807268555604321170121)
                    ·
                      refine ⟨178355451416703240877591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 237807268555604321170121 178355451416703240877591)
                      ·
                        rfl

theorem cell23_347346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_347346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347346 prefixEnd_347346 := by exact prefixLift 347346
  have htrace : WordTrace (prefixWord ++ tailWord_347346) baseStart_347346 baseEnd_347346 := by
    simpa [prefixWord, tailWord_347346, baseEnd_347346] using wordTrace_append hprefix tailTrace_347346
  have hstable : (prefixWord ++ tailWord_347346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347346).length < 2 ^ (prefixWord ++ tailWord_347346).sum := by decide
  have hdescent : baseEnd_347346 < baseStart_347346 := by decide
  rcases family_descends (prefixWord ++ tailWord_347346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347359 : List Nat := [1, 1, 2, 3, 2, 1, 4, 3, 1, 1, 4]
def baseStart_347359 : Nat := 118140960795 + 347359 * 2 ^ 59
def prefixEnd_347359 : Nat := 4983230072969 + 3 ^ 40 * 347359 * 2
def baseEnd_347359 : Nat := 178362126665211690015031

theorem tailTrace_347359 : CollatzResearch.WordTrace tailWord_347359 prefixEnd_347359 178362126665211690015031 := by
  unfold tailWord_347359
  simp only [CollatzResearch.WordTrace]
  refine ⟨12669223548585142039269131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8446149032390094692846087 12669223548585142039269131)
  ·
    refine ⟨19003835322877713058903697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12669223548585142039269131 19003835322877713058903697)
    ·
      refine ⟨14252876492158284794177773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19003835322877713058903697 14252876492158284794177773)
      ·
        refine ⟨5344828684559356797816665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14252876492158284794177773 5344828684559356797816665)
        ·
          refine ⟨4008621513419517598362499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5344828684559356797816665 4008621513419517598362499)
          ·
            refine ⟨6012932270129276397543749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4008621513419517598362499 6012932270129276397543749)
            ·
              refine ⟨1127424800649239324539453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6012932270129276397543749 1127424800649239324539453)
              ·
                refine ⟨422784300243464746702295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1127424800649239324539453 422784300243464746702295)
                ·
                  refine ⟨634176450365197120053443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 422784300243464746702295 634176450365197120053443)
                  ·
                    refine ⟨951264675547795680080165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 634176450365197120053443 951264675547795680080165)
                    ·
                      refine ⟨178362126665211690015031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 951264675547795680080165 178362126665211690015031)
                      ·
                        rfl

theorem cell23_347359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_347359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347359 prefixEnd_347359 := by exact prefixLift 347359
  have htrace : WordTrace (prefixWord ++ tailWord_347359) baseStart_347359 baseEnd_347359 := by
    simpa [prefixWord, tailWord_347359, baseEnd_347359] using wordTrace_append hprefix tailTrace_347359
  have hstable : (prefixWord ++ tailWord_347359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347359).length < 2 ^ (prefixWord ++ tailWord_347359).sum := by decide
  have hdescent : baseEnd_347359 < baseStart_347359 := by decide
  rcases family_descends (prefixWord ++ tailWord_347359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347370 : List Nat := [3, 1, 3, 1, 1, 4, 3, 2, 1, 1, 3]
def baseStart_347370 : Nat := 118140960795 + 347370 * 2 ^ 59
def prefixEnd_347370 : Nat := 4983230072969 + 3 ^ 40 * 347370 * 2
def baseEnd_347370 : Nat := 178367774952411146977481

theorem tailTrace_347370 : CollatzResearch.WordTrace tailWord_347370 prefixEnd_347370 178367774952411146977481 := by
  unfold tailWord_347370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3167406187886322729479891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8446416501030193945279709 3167406187886322729479891)
  ·
    refine ⟨4751109281829484094219837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3167406187886322729479891 4751109281829484094219837)
    ·
      refine ⟨1781665980686056535332439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4751109281829484094219837 1781665980686056535332439)
      ·
        refine ⟨2672498971029084802998659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1781665980686056535332439 2672498971029084802998659)
        ·
          refine ⟨4008748456543627204497989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2672498971029084802998659 4008748456543627204497989)
          ·
            refine ⟨751640335601930100843373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4008748456543627204497989 751640335601930100843373)
            ·
              refine ⟨281865125850723787816265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 751640335601930100843373 281865125850723787816265)
              ·
                refine ⟨211398844388042840862199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281865125850723787816265 211398844388042840862199)
                ·
                  refine ⟨317098266582064261293299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211398844388042840862199 317098266582064261293299)
                  ·
                    refine ⟨475647399873096391939949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 317098266582064261293299 475647399873096391939949)
                    ·
                      refine ⟨178367774952411146977481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 475647399873096391939949 178367774952411146977481)
                      ·
                        rfl

theorem cell23_347370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_347370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347370 prefixEnd_347370 := by exact prefixLift 347370
  have htrace : WordTrace (prefixWord ++ tailWord_347370) baseStart_347370 baseEnd_347370 := by
    simpa [prefixWord, tailWord_347370, baseEnd_347370] using wordTrace_append hprefix tailTrace_347370
  have hstable : (prefixWord ++ tailWord_347370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347370).length < 2 ^ (prefixWord ++ tailWord_347370).sum := by decide
  have hdescent : baseEnd_347370 < baseStart_347370 := by decide
  rcases family_descends (prefixWord ++ tailWord_347370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347372 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 6]
def baseStart_347372 : Nat := 118140960795 + 347372 * 2 ^ 59
def prefixEnd_347372 : Nat := 4983230072969 + 3 ^ 40 * 347372 * 2
def baseEnd_347372 : Nat := 178368801913720139152471

theorem tailTrace_347372 : CollatzResearch.WordTrace tailWord_347372 prefixEnd_347372 178368801913720139152471 := by
  unfold tailWord_347372
  simp only [CollatzResearch.WordTrace]
  refine ⟨6334848848769022629746185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8446465131692030172994913 6334848848769022629746185)
  ·
    refine ⟨4751136636576766972309639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6334848848769022629746185 4751136636576766972309639)
    ·
      refine ⟨7126704954865150458464459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4751136636576766972309639 7126704954865150458464459)
      ·
        refine ⟨10690057432297725687696689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7126704954865150458464459 10690057432297725687696689)
        ·
          refine ⟨8017543074223294265772517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10690057432297725687696689 8017543074223294265772517)
          ·
            refine ⟨1503289326416867674832347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8017543074223294265772517 1503289326416867674832347)
            ·
              refine ⟨2254933989625301512248521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503289326416867674832347 2254933989625301512248521)
              ·
                refine ⟨1691200492218976134186391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2254933989625301512248521 1691200492218976134186391)
                ·
                  refine ⟨2536800738328464201279587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1691200492218976134186391 2536800738328464201279587)
                  ·
                    refine ⟨3805201107492696301919381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2536800738328464201279587 3805201107492696301919381)
                    ·
                      refine ⟨178368801913720139152471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3805201107492696301919381 178368801913720139152471)
                      ·
                        rfl

theorem cell23_347372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_347372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347372 prefixEnd_347372 := by exact prefixLift 347372
  have htrace : WordTrace (prefixWord ++ tailWord_347372) baseStart_347372 baseEnd_347372 := by
    simpa [prefixWord, tailWord_347372, baseEnd_347372] using wordTrace_append hprefix tailTrace_347372
  have hstable : (prefixWord ++ tailWord_347372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347372).length < 2 ^ (prefixWord ++ tailWord_347372).sum := by decide
  have hdescent : baseEnd_347372 < baseStart_347372 := by decide
  rcases family_descends (prefixWord ++ tailWord_347372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347396 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_347396 : Nat := 118140960795 + 347396 * 2 ^ 59
def prefixEnd_347396 : Nat := 4983230072969 + 3 ^ 40 * 347396 * 2
def baseEnd_347396 : Nat := 178381125449428045252361

theorem tailTrace_347396 : CollatzResearch.WordTrace tailWord_347396 prefixEnd_347396 178381125449428045252361 := by
  unfold tailWord_347396
  simp only [CollatzResearch.WordTrace]
  refine ⟨6335286524725548679183021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8447048699634064905577361 6335286524725548679183021)
  ·
    refine ⟨2375732446772080754693633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6335286524725548679183021 2375732446772080754693633)
    ·
      refine ⟨1781799335079060566020225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2375732446772080754693633 1781799335079060566020225)
      ·
        refine ⟨1336349501309295424515169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1781799335079060566020225 1336349501309295424515169)
        ·
          refine ⟨1002262125981971568386377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1336349501309295424515169 1002262125981971568386377)
          ·
            refine ⟨751696594486478676289783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1002262125981971568386377 751696594486478676289783)
            ·
              refine ⟨1127544891729718014434675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751696594486478676289783 1127544891729718014434675)
              ·
                refine ⟨1691317337594577021652013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1127544891729718014434675 1691317337594577021652013)
                ·
                  refine ⟨634244001597966383119505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1691317337594577021652013 634244001597966383119505)
                  ·
                    refine ⟨475683001198474787339629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 634244001597966383119505 475683001198474787339629)
                    ·
                      refine ⟨178381125449428045252361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 475683001198474787339629 178381125449428045252361)
                      ·
                        rfl

theorem cell23_347396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_347396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347396 prefixEnd_347396 := by exact prefixLift 347396
  have htrace : WordTrace (prefixWord ++ tailWord_347396) baseStart_347396 baseEnd_347396 := by
    simpa [prefixWord, tailWord_347396, baseEnd_347396] using wordTrace_append hprefix tailTrace_347396
  have hstable : (prefixWord ++ tailWord_347396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347396).length < 2 ^ (prefixWord ++ tailWord_347396).sum := by decide
  have hdescent : baseEnd_347396 < baseStart_347396 := by decide
  rcases family_descends (prefixWord ++ tailWord_347396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347409 : List Nat := [1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 3]
def baseStart_347409 : Nat := 118140960795 + 347409 * 2 ^ 59
def prefixEnd_347409 : Nat := 4983230072969 + 3 ^ 40 * 347409 * 2
def baseEnd_347409 : Nat := 178387800697936494389801

theorem tailTrace_347409 : CollatzResearch.WordTrace tailWord_347409 prefixEnd_347409 178387800697936494389801 := by
  unfold tailWord_347409
  simp only [CollatzResearch.WordTrace]
  refine ⟨12671047198404000578589281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8447364798936000385726187 12671047198404000578589281)
  ·
    refine ⟨9503285398803000433941961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12671047198404000578589281 9503285398803000433941961)
    ·
      refine ⟨7127464049102250325456471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9503285398803000433941961 7127464049102250325456471)
      ·
        refine ⟨10691196073653375488184707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7127464049102250325456471 10691196073653375488184707)
        ·
          refine ⟨16036794110480063232277061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10691196073653375488184707 16036794110480063232277061)
          ·
            refine ⟨3006898895715011856051949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16036794110480063232277061 3006898895715011856051949)
            ·
              refine ⟨1127587085893129446019481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3006898895715011856051949 1127587085893129446019481)
              ·
                refine ⟨845690314419847084514611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1127587085893129446019481 845690314419847084514611)
                ·
                  refine ⟨1268535471629770626771917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 845690314419847084514611 1268535471629770626771917)
                  ·
                    refine ⟨475700801861163985039469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1268535471629770626771917 475700801861163985039469)
                    ·
                      refine ⟨178387800697936494389801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 475700801861163985039469 178387800697936494389801)
                      ·
                        rfl

theorem cell23_347409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_347409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347409 prefixEnd_347409 := by exact prefixLift 347409
  have htrace : WordTrace (prefixWord ++ tailWord_347409) baseStart_347409 baseEnd_347409 := by
    simpa [prefixWord, tailWord_347409, baseEnd_347409] using wordTrace_append hprefix tailTrace_347409
  have hstable : (prefixWord ++ tailWord_347409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347409).length < 2 ^ (prefixWord ++ tailWord_347409).sum := by decide
  have hdescent : baseEnd_347409 < baseStart_347409 := by decide
  rcases family_descends (prefixWord ++ tailWord_347409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347427 : List Nat := [1, 1, 1, 4, 2, 5, 2, 2, 1, 2, 2]
def baseStart_347427 : Nat := 118140960795 + 347427 * 2 ^ 59
def prefixEnd_347427 : Nat := 4983230072969 + 3 ^ 40 * 347427 * 2
def baseEnd_347427 : Nat := 178397043349717423964719

theorem tailTrace_347427 : CollatzResearch.WordTrace tailWord_347427 prefixEnd_347427 178397043349717423964719 := by
  unfold tailWord_347427
  simp only [CollatzResearch.WordTrace]
  refine ⟨12671703712338789652744535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8447802474892526435163023 12671703712338789652744535)
  ·
    refine ⟨19007555568508184479116803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12671703712338789652744535 19007555568508184479116803)
    ·
      refine ⟨28511333352762276718675205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19007555568508184479116803 28511333352762276718675205)
      ·
        refine ⟨5345875003642926884751601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28511333352762276718675205 5345875003642926884751601)
        ·
          refine ⟨4009406252732195163563701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5345875003642926884751601 4009406252732195163563701)
          ·
            refine ⟨375881836193643296584097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4009406252732195163563701 375881836193643296584097)
            ·
              refine ⟨281911377145232472438073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375881836193643296584097 281911377145232472438073)
              ·
                refine ⟨211433532858924354328555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281911377145232472438073 211433532858924354328555)
                ·
                  refine ⟨317150299288386531492833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211433532858924354328555 317150299288386531492833)
                  ·
                    refine ⟨237862724466289898619625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 317150299288386531492833 237862724466289898619625)
                    ·
                      refine ⟨178397043349717423964719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 237862724466289898619625 178397043349717423964719)
                      ·
                        rfl

theorem cell23_347427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_347427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347427 prefixEnd_347427 := by exact prefixLift 347427
  have htrace : WordTrace (prefixWord ++ tailWord_347427) baseStart_347427 baseEnd_347427 := by
    simpa [prefixWord, tailWord_347427, baseEnd_347427] using wordTrace_append hprefix tailTrace_347427
  have hstable : (prefixWord ++ tailWord_347427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347427).length < 2 ^ (prefixWord ++ tailWord_347427).sum := by decide
  have hdescent : baseEnd_347427 < baseStart_347427 := by decide
  rcases family_descends (prefixWord ++ tailWord_347427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347472 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 9]
def baseStart_347472 : Nat := 118140960795 + 347472 * 2 ^ 59
def prefixEnd_347472 : Nat := 4983230072969 + 3 ^ 40 * 347472 * 2
def baseEnd_347472 : Nat := 19824461108796638655779

theorem tailTrace_347472 : CollatzResearch.WordTrace tailWord_347472 prefixEnd_347472 19824461108796638655779 := by
  unfold tailWord_347472
  simp only [CollatzResearch.WordTrace]
  refine ⟨6336672498587881169066335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8448896664783841558755113 6336672498587881169066335)
  ·
    refine ⟨9505008747881821753599503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6336672498587881169066335 9505008747881821753599503)
    ·
      refine ⟨14257513121822732630399255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9505008747881821753599503 14257513121822732630399255)
      ·
        refine ⟨21386269682734098945598883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14257513121822732630399255 21386269682734098945598883)
        ·
          refine ⟨32079404524101148418398325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21386269682734098945598883 32079404524101148418398325)
          ·
            refine ⟨3007444174134482664224843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32079404524101148418398325 3007444174134482664224843)
            ·
              refine ⟨4511166261201723996337265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3007444174134482664224843 4511166261201723996337265)
              ·
                refine ⟨3383374695901292997252949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4511166261201723996337265 3383374695901292997252949)
                ·
                  refine ⟨19824461108796638655779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3383374695901292997252949 19824461108796638655779)
                  ·
                    rfl

theorem cell23_347472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 9].length) (baseStart_347472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347472 prefixEnd_347472 := by exact prefixLift 347472
  have htrace : WordTrace (prefixWord ++ tailWord_347472) baseStart_347472 baseEnd_347472 := by
    simpa [prefixWord, tailWord_347472, baseEnd_347472] using wordTrace_append hprefix tailTrace_347472
  have hstable : (prefixWord ++ tailWord_347472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347472).length < 2 ^ (prefixWord ++ tailWord_347472).sum := by decide
  have hdescent : baseEnd_347472 < baseStart_347472 := by decide
  rcases family_descends (prefixWord ++ tailWord_347472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347479 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 4]
def baseStart_347479 : Nat := 118140960795 + 347479 * 2 ^ 59
def prefixEnd_347479 : Nat := 4983230072969 + 3 ^ 40 * 347479 * 2
def baseEnd_347479 : Nat := 178423744343751220514479

theorem tailTrace_347479 : CollatzResearch.WordTrace tailWord_347479 prefixEnd_347479 178423744343751220514479 := by
  unfold tailWord_347479
  simp only [CollatzResearch.WordTrace]
  refine ⟨12673600308150402533637491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8449066872100268355758327 12673600308150402533637491)
  ·
    refine ⟨19010400462225603800456237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12673600308150402533637491 19010400462225603800456237)
    ·
      refine ⟨7128900173334601425171089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19010400462225603800456237 7128900173334601425171089)
      ·
        refine ⟨5346675130000951068878317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7128900173334601425171089 5346675130000951068878317)
        ·
          refine ⟨2005003173750356650829369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5346675130000951068878317 2005003173750356650829369)
          ·
            refine ⟨1503752380312767488122027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2005003173750356650829369 1503752380312767488122027)
            ·
              refine ⟨2255628570469151232183041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503752380312767488122027 2255628570469151232183041)
              ·
                refine ⟨1691721427851863424137281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2255628570469151232183041 1691721427851863424137281)
                ·
                  refine ⟨1268791070888897568102961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1691721427851863424137281 1268791070888897568102961)
                  ·
                    refine ⟨951593303166673176077221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1268791070888897568102961 951593303166673176077221)
                    ·
                      refine ⟨178423744343751220514479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 951593303166673176077221 178423744343751220514479)
                      ·
                        rfl

theorem cell23_347479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_347479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347479 prefixEnd_347479 := by exact prefixLift 347479
  have htrace : WordTrace (prefixWord ++ tailWord_347479) baseStart_347479 baseEnd_347479 := by
    simpa [prefixWord, tailWord_347479, baseEnd_347479] using wordTrace_append hprefix tailTrace_347479
  have hstable : (prefixWord ++ tailWord_347479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347479).length < 2 ^ (prefixWord ++ tailWord_347479).sum := by decide
  have hdescent : baseEnd_347479 < baseStart_347479 := by decide
  rcases family_descends (prefixWord ++ tailWord_347479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347523 : List Nat := [1, 1, 1, 3, 5, 3, 1, 3, 5]
def baseStart_347523 : Nat := 118140960795 + 347523 * 2 ^ 59
def prefixEnd_347523 : Nat := 4983230072969 + 3 ^ 40 * 347523 * 2
def baseEnd_347523 : Nat := 19827370832505449818253

theorem tailTrace_347523 : CollatzResearch.WordTrace tailWord_347523 prefixEnd_347523 19827370832505449818253 := by
  unfold tailWord_347523
  simp only [CollatzResearch.WordTrace]
  refine ⟨12675205119990998048239223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8450136746660665365492815 12675205119990998048239223)
  ·
    refine ⟨19012807679986497072358835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12675205119990998048239223 19012807679986497072358835)
    ·
      refine ⟨28519211519979745608538253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19012807679986497072358835 28519211519979745608538253)
      ·
        refine ⟨10694704319992404603201845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28519211519979745608538253 10694704319992404603201845)
        ·
          refine ⟨1002628529999287931550173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10694704319992404603201845 1002628529999287931550173)
          ·
            refine ⟨375985698749732974331315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1002628529999287931550173 375985698749732974331315)
            ·
              refine ⟨563978548124599461496973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375985698749732974331315 563978548124599461496973)
              ·
                refine ⟨211491955546724798061365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 563978548124599461496973 211491955546724798061365)
                ·
                  refine ⟨19827370832505449818253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 211491955546724798061365 19827370832505449818253)
                  ·
                    rfl

theorem cell23_347523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 5].length) (baseStart_347523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347523 prefixEnd_347523 := by exact prefixLift 347523
  have htrace : WordTrace (prefixWord ++ tailWord_347523) baseStart_347523 baseEnd_347523 := by
    simpa [prefixWord, tailWord_347523, baseEnd_347523] using wordTrace_append hprefix tailTrace_347523
  have hstable : (prefixWord ++ tailWord_347523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347523).length < 2 ^ (prefixWord ++ tailWord_347523).sum := by decide
  have hdescent : baseEnd_347523 < baseStart_347523 := by decide
  rcases family_descends (prefixWord ++ tailWord_347523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347540 : List Nat := [2, 4, 2, 1, 2, 2, 3, 2, 5]
def baseStart_347540 : Nat := 118140960795 + 347540 * 2 ^ 59
def prefixEnd_347540 : Nat := 4983230072969 + 3 ^ 40 * 347540 * 2
def baseEnd_347540 : Nat := 19828340740408386872411

theorem tailTrace_347540 : CollatzResearch.WordTrace tailWord_347540 prefixEnd_347540 19828340740408386872411 := by
  unfold tailWord_347540
  simp only [CollatzResearch.WordTrace]
  refine ⟨6337912580464704975804037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8450550107286273301072049 6337912580464704975804037)
  ·
    refine ⟨1188358608837132182963257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6337912580464704975804037 1188358608837132182963257)
    ·
      refine ⟨891268956627849137222443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1188358608837132182963257 891268956627849137222443)
      ·
        refine ⟨1336903434941773705833665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891268956627849137222443 1336903434941773705833665)
        ·
          refine ⟨1002677576206330279375249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1336903434941773705833665 1002677576206330279375249)
          ·
            refine ⟨752008182154747709531437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1002677576206330279375249 752008182154747709531437)
            ·
              refine ⟨282003068308030391074289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 752008182154747709531437 282003068308030391074289)
              ·
                refine ⟨211502301231022793305717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282003068308030391074289 211502301231022793305717)
                ·
                  refine ⟨19828340740408386872411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 211502301231022793305717 19828340740408386872411)
                  ·
                    rfl

theorem cell23_347540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_347540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347540 prefixEnd_347540 := by exact prefixLift 347540
  have htrace : WordTrace (prefixWord ++ tailWord_347540) baseStart_347540 baseEnd_347540 := by
    simpa [prefixWord, tailWord_347540, baseEnd_347540] using wordTrace_append hprefix tailTrace_347540
  have hstable : (prefixWord ++ tailWord_347540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347540).length < 2 ^ (prefixWord ++ tailWord_347540).sum := by decide
  have hdescent : baseEnd_347540 < baseStart_347540 := by decide
  rcases family_descends (prefixWord ++ tailWord_347540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347556 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 1, 6, 2]
def baseStart_347556 : Nat := 118140960795 + 347556 * 2 ^ 59
def prefixEnd_347556 : Nat := 4983230072969 + 3 ^ 40 * 347556 * 2
def baseEnd_347556 : Nat := 178463282354147419251625

theorem tailTrace_347556 : CollatzResearch.WordTrace tailWord_347556 prefixEnd_347556 178463282354147419251625 := by
  unfold tailWord_347556
  simp only [CollatzResearch.WordTrace]
  refine ⟨6338204364435722342095261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8450939152580963122793681 6338204364435722342095261)
  ·
    refine ⟨2376826636663395878285723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6338204364435722342095261 2376826636663395878285723)
    ·
      refine ⟨3565239954995093817428585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2376826636663395878285723 3565239954995093817428585)
      ·
        refine ⟨2673929966246320363071439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3565239954995093817428585 2673929966246320363071439)
        ·
          refine ⟨4010894949369480544607159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2673929966246320363071439 4010894949369480544607159)
          ·
            refine ⟨6016342424054220816910739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4010894949369480544607159 6016342424054220816910739)
            ·
              refine ⟨9024513636081331225366109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6016342424054220816910739 9024513636081331225366109)
              ·
                refine ⟨3384192613530499209512291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9024513636081331225366109 3384192613530499209512291)
                ·
                  refine ⟨5076288920295748814268437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3384192613530499209512291 5076288920295748814268437)
                  ·
                    refine ⟨237951043138863225668833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5076288920295748814268437 237951043138863225668833)
                    ·
                      refine ⟨178463282354147419251625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 237951043138863225668833 178463282354147419251625)
                      ·
                        rfl

theorem cell23_347556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_347556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347556 prefixEnd_347556 := by exact prefixLift 347556
  have htrace : WordTrace (prefixWord ++ tailWord_347556) baseStart_347556 baseEnd_347556 := by
    simpa [prefixWord, tailWord_347556, baseEnd_347556] using wordTrace_append hprefix tailTrace_347556
  have hstable : (prefixWord ++ tailWord_347556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347556).length < 2 ^ (prefixWord ++ tailWord_347556).sum := by decide
  have hdescent : baseEnd_347556 < baseStart_347556 := by decide
  rcases family_descends (prefixWord ++ tailWord_347556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347573 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_347573 : Nat := 118140960795 + 347573 * 2 ^ 59
def prefixEnd_347573 : Nat := 4983230072969 + 3 ^ 40 * 347573 * 2
def baseEnd_347573 : Nat := 178472011525273852739047

theorem tailTrace_347573 : CollatzResearch.WordTrace tailWord_347573 prefixEnd_347573 178472011525273852739047 := by
  unfold tailWord_347573
  simp only [CollatzResearch.WordTrace]
  refine ⟨12677028769809856587559373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8451352513206571058372915 12677028769809856587559373)
  ·
    refine ⟨4753885788678696220334765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12677028769809856587559373 4753885788678696220334765)
    ·
      refine ⟨1782707170754511082625537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4753885788678696220334765 1782707170754511082625537)
      ·
        refine ⟨1337030378065883311969153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1782707170754511082625537 1337030378065883311969153)
        ·
          refine ⟨1002772783549412483976865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1337030378065883311969153 1002772783549412483976865)
          ·
            refine ⟨752079587662059362982649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1002772783549412483976865 752079587662059362982649)
            ·
              refine ⟨564059690746544522236987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752079587662059362982649 564059690746544522236987)
              ·
                refine ⟨846089536119816783355481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564059690746544522236987 846089536119816783355481)
                ·
                  refine ⟨634567152089862587516611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 846089536119816783355481 634567152089862587516611)
                  ·
                    refine ⟨951850728134793881274917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 634567152089862587516611 951850728134793881274917)
                    ·
                      refine ⟨178472011525273852739047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 951850728134793881274917 178472011525273852739047)
                      ·
                        rfl

theorem cell23_347573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_347573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347573 prefixEnd_347573 := by exact prefixLift 347573
  have htrace : WordTrace (prefixWord ++ tailWord_347573) baseStart_347573 baseEnd_347573 := by
    simpa [prefixWord, tailWord_347573, baseEnd_347573] using wordTrace_append hprefix tailTrace_347573
  have hstable : (prefixWord ++ tailWord_347573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347573).length < 2 ^ (prefixWord ++ tailWord_347573).sum := by decide
  have hdescent : baseEnd_347573 < baseStart_347573 := by decide
  rcases family_descends (prefixWord ++ tailWord_347573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347576 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 2, 2, 3]
def baseStart_347576 : Nat := 118140960795 + 347576 * 2 ^ 59
def prefixEnd_347576 : Nat := 4983230072969 + 3 ^ 40 * 347576 * 2
def baseEnd_347576 : Nat := 178473551967237341001533

theorem tailTrace_347576 : CollatzResearch.WordTrace tailWord_347576 prefixEnd_347576 178473551967237341001533 := by
  unfold tailWord_347576
  simp only [CollatzResearch.WordTrace]
  refine ⟨6338569094399494049959291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8451425459199325399945721 6338569094399494049959291)
  ·
    refine ⟨9507853641599241074938937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6338569094399494049959291 9507853641599241074938937)
    ·
      refine ⟨7130890231199430806204203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9507853641599241074938937 7130890231199430806204203)
      ·
        refine ⟨10696335346799146209306305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7130890231199430806204203 10696335346799146209306305)
        ·
          refine ⟨8022251510099359656979729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10696335346799146209306305 8022251510099359656979729)
          ·
            refine ⟨6016688632574519742734797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8022251510099359656979729 6016688632574519742734797)
            ·
              refine ⟨2256258237215444903525549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6016688632574519742734797 2256258237215444903525549)
              ·
                refine ⟨846096838955791838822081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2256258237215444903525549 846096838955791838822081)
                ·
                  refine ⟨634572629216843879116561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 846096838955791838822081 634572629216843879116561)
                  ·
                    refine ⟨475929471912632909337421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 634572629216843879116561 475929471912632909337421)
                    ·
                      refine ⟨178473551967237341001533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 475929471912632909337421 178473551967237341001533)
                      ·
                        rfl

theorem cell23_347576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_347576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347576 prefixEnd_347576 := by exact prefixLift 347576
  have htrace : WordTrace (prefixWord ++ tailWord_347576) baseStart_347576 baseEnd_347576 := by
    simpa [prefixWord, tailWord_347576, baseEnd_347576] using wordTrace_append hprefix tailTrace_347576
  have hstable : (prefixWord ++ tailWord_347576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347576).length < 2 ^ (prefixWord ++ tailWord_347576).sum := by decide
  have hdescent : baseEnd_347576 < baseStart_347576 := by decide
  rcases family_descends (prefixWord ++ tailWord_347576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347596 : List Nat := [2, 2, 1, 4, 2, 1, 1, 4, 6]
def baseStart_347596 : Nat := 118140960795 + 347596 * 2 ^ 59
def prefixEnd_347596 : Nat := 4983230072969 + 3 ^ 40 * 347596 * 2
def baseEnd_347596 : Nat := 19831535731147473639049

theorem tailTrace_347596 : CollatzResearch.WordTrace tailWord_347596 prefixEnd_347596 19831535731147473639049 := by
  unfold tailWord_347596
  simp only [CollatzResearch.WordTrace]
  refine ⟨6338933824363265757823321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8451911765817687677097761 6338933824363265757823321)
  ·
    refine ⟨4754200368272449318367491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6338933824363265757823321 4754200368272449318367491)
    ·
      refine ⟨7131300552408673977551237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4754200368272449318367491 7131300552408673977551237)
      ·
        refine ⟨1337118853576626370790857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7131300552408673977551237 1337118853576626370790857)
        ·
          refine ⟨1002839140182469778093143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1337118853576626370790857 1002839140182469778093143)
          ·
            refine ⟨1504258710273704667139715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002839140182469778093143 1504258710273704667139715)
            ·
              refine ⟨2256388065410557000709573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504258710273704667139715 2256388065410557000709573)
              ·
                refine ⟨423072762264479437633045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2256388065410557000709573 423072762264479437633045)
                ·
                  refine ⟨19831535731147473639049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 423072762264479437633045 19831535731147473639049)
                  ·
                    rfl

theorem cell23_347596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 6].length) (baseStart_347596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347596 prefixEnd_347596 := by exact prefixLift 347596
  have htrace : WordTrace (prefixWord ++ tailWord_347596) baseStart_347596 baseEnd_347596 := by
    simpa [prefixWord, tailWord_347596, baseEnd_347596] using wordTrace_append hprefix tailTrace_347596
  have hstable : (prefixWord ++ tailWord_347596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347596).length < 2 ^ (prefixWord ++ tailWord_347596).sum := by decide
  have hdescent : baseEnd_347596 < baseStart_347596 := by decide
  rcases family_descends (prefixWord ++ tailWord_347596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347623 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 5, 1, 3]
def baseStart_347623 : Nat := 118140960795 + 347623 * 2 ^ 59
def prefixEnd_347623 : Nat := 4983230072969 + 3 ^ 40 * 347623 * 2
def baseEnd_347623 : Nat := 178497685557998657113817

theorem tailTrace_347623 : CollatzResearch.WordTrace tailWord_347623 prefixEnd_347623 178497685557998657113817 := by
  unfold tailWord_347623
  simp only [CollatzResearch.WordTrace]
  refine ⟨12678852419628715126879523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8452568279752476751253015 12678852419628715126879523)
  ·
    refine ⟨19018278629443072690319285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12678852419628715126879523 19018278629443072690319285)
    ·
      refine ⟨1782963621510288064717433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19018278629443072690319285 1782963621510288064717433)
      ·
        refine ⟨1337222716132716048538075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1782963621510288064717433 1337222716132716048538075)
        ·
          refine ⟨2005834074199074072807113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337222716132716048538075 2005834074199074072807113)
          ·
            refine ⟨1504375555649305554605335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2005834074199074072807113 1504375555649305554605335)
            ·
              refine ⟨2256563333473958331908003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504375555649305554605335 2256563333473958331908003)
              ·
                refine ⟨3384845000210937497862005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2256563333473958331908003 3384845000210937497862005)
                ·
                  refine ⟨317329218769775390424563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3384845000210937497862005 317329218769775390424563)
                  ·
                    refine ⟨475993828154663085636845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 317329218769775390424563 475993828154663085636845)
                    ·
                      refine ⟨178497685557998657113817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 475993828154663085636845 178497685557998657113817)
                      ·
                        rfl

theorem cell23_347623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_347623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347623 prefixEnd_347623 := by exact prefixLift 347623
  have htrace : WordTrace (prefixWord ++ tailWord_347623) baseStart_347623 baseEnd_347623 := by
    simpa [prefixWord, tailWord_347623, baseEnd_347623] using wordTrace_append hprefix tailTrace_347623
  have hstable : (prefixWord ++ tailWord_347623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347623).length < 2 ^ (prefixWord ++ tailWord_347623).sum := by decide
  have hdescent : baseEnd_347623 < baseStart_347623 := by decide
  rcases family_descends (prefixWord ++ tailWord_347623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347633 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 1, 5, 2]
def baseStart_347633 : Nat := 118140960795 + 347633 * 2 ^ 59
def prefixEnd_347633 : Nat := 4983230072969 + 3 ^ 40 * 347633 * 2
def baseEnd_347633 : Nat := 178502820364543617988771

theorem tailTrace_347633 : CollatzResearch.WordTrace tailWord_347633 prefixEnd_347633 178502820364543617988771 := by
  unfold tailWord_347633
  simp only [CollatzResearch.WordTrace]
  refine ⟨12679217149592486834743553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8452811433061657889829035 12679217149592486834743553)
  ·
    refine ⟨9509412862194365126057665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12679217149592486834743553 9509412862194365126057665)
    ·
      refine ⟨7132059646645773844543249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9509412862194365126057665 7132059646645773844543249)
      ·
        refine ⟨5349044734984330383407437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7132059646645773844543249 5349044734984330383407437)
        ·
          refine ⟨2005891775619123893777789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5349044734984330383407437 2005891775619123893777789)
          ·
            refine ⟨752209415857171460166671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2005891775619123893777789 752209415857171460166671)
            ·
              refine ⟨1128314123785757190250007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752209415857171460166671 1128314123785757190250007)
              ·
                refine ⟨1692471185678635785375011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128314123785757190250007 1692471185678635785375011)
                ·
                  refine ⟨2538706778517953678062517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692471185678635785375011 2538706778517953678062517)
                  ·
                    refine ⟨238003760486058157318361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2538706778517953678062517 238003760486058157318361)
                    ·
                      refine ⟨178502820364543617988771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 238003760486058157318361 178502820364543617988771)
                      ·
                        rfl

theorem cell23_347633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_347633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347633 prefixEnd_347633 := by exact prefixLift 347633
  have htrace : WordTrace (prefixWord ++ tailWord_347633) baseStart_347633 baseEnd_347633 := by
    simpa [prefixWord, tailWord_347633, baseEnd_347633] using wordTrace_append hprefix tailTrace_347633
  have hstable : (prefixWord ++ tailWord_347633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347633).length < 2 ^ (prefixWord ++ tailWord_347633).sum := by decide
  have hdescent : baseEnd_347633 < baseStart_347633 := by decide
  rcases family_descends (prefixWord ++ tailWord_347633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347639 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 3, 6]
def baseStart_347639 : Nat := 118140960795 + 347639 * 2 ^ 59
def prefixEnd_347639 : Nat := 4983230072969 + 3 ^ 40 * 347639 * 2
def baseEnd_347639 : Nat := 59501967082823531504581

theorem tailTrace_347639 : CollatzResearch.WordTrace tailWord_347639 prefixEnd_347639 59501967082823531504581 := by
  unfold tailWord_347639
  simp only [CollatzResearch.WordTrace]
  refine ⟨12679435987570749859461971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8452957325047166572974647 12679435987570749859461971)
  ·
    refine ⟨19019153981356124789192957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12679435987570749859461971 19019153981356124789192957)
    ·
      refine ⟨7132182743008546795947359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19019153981356124789192957 7132182743008546795947359)
      ·
        refine ⟨10698274114512820193921039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7132182743008546795947359 10698274114512820193921039)
        ·
          refine ⟨16047411171769230290881559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10698274114512820193921039 16047411171769230290881559)
          ·
            refine ⟨24071116757653845436322339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16047411171769230290881559 24071116757653845436322339)
            ·
              refine ⟨36106675136480768154483509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24071116757653845436322339 36106675136480768154483509)
              ·
                refine ⟨3385000794045072014482829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36106675136480768154483509 3385000794045072014482829)
                ·
                  refine ⟨1269375297766902005431061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3385000794045072014482829 1269375297766902005431061)
                  ·
                    refine ⟨59501967082823531504581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1269375297766902005431061 59501967082823531504581)
                    ·
                      rfl

theorem cell23_347639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_347639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347639 prefixEnd_347639 := by exact prefixLift 347639
  have htrace : WordTrace (prefixWord ++ tailWord_347639) baseStart_347639 baseEnd_347639 := by
    simpa [prefixWord, tailWord_347639, baseEnd_347639] using wordTrace_append hprefix tailTrace_347639
  have hstable : (prefixWord ++ tailWord_347639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347639).length < 2 ^ (prefixWord ++ tailWord_347639).sum := by decide
  have hdescent : baseEnd_347639 < baseStart_347639 := by decide
  rcases family_descends (prefixWord ++ tailWord_347639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347640 : List Nat := [2, 1, 2, 1, 1, 5, 1, 5, 1, 1, 3]
def baseStart_347640 : Nat := 118140960795 + 347640 * 2 ^ 59
def prefixEnd_347640 : Nat := 4983230072969 + 3 ^ 40 * 347640 * 2
def baseEnd_347640 : Nat := 178506414729125090601239

theorem tailTrace_347640 : CollatzResearch.WordTrace tailWord_347640 prefixEnd_347640 178506414729125090601239 := by
  unfold tailWord_347640
  simp only [CollatzResearch.WordTrace]
  refine ⟨6339736230283563515124187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8452981640378084686832249 6339736230283563515124187)
  ·
    refine ⟨9509604345425345272686281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6339736230283563515124187 9509604345425345272686281)
    ·
      refine ⟨7132203259069008954514711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9509604345425345272686281 7132203259069008954514711)
      ·
        refine ⟨10698304888603513431772067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7132203259069008954514711 10698304888603513431772067)
        ·
          refine ⟨16047457332905270147658101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10698304888603513431772067 16047457332905270147658101)
          ·
            refine ⟨1504449124959869076342947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16047457332905270147658101 1504449124959869076342947)
            ·
              refine ⟨2256673687439803614514421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504449124959869076342947 2256673687439803614514421)
              ·
                refine ⟨211563158197481588860727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2256673687439803614514421 211563158197481588860727)
                ·
                  refine ⟨317344737296222383291091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211563158197481588860727 317344737296222383291091)
                  ·
                    refine ⟨476017105944333574936637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 317344737296222383291091 476017105944333574936637)
                    ·
                      refine ⟨178506414729125090601239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 476017105944333574936637 178506414729125090601239)
                      ·
                        rfl

theorem cell23_347640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 1, 1, 3].length) (baseStart_347640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347640 prefixEnd_347640 := by exact prefixLift 347640
  have htrace : WordTrace (prefixWord ++ tailWord_347640) baseStart_347640 baseEnd_347640 := by
    simpa [prefixWord, tailWord_347640, baseEnd_347640] using wordTrace_append hprefix tailTrace_347640
  have hstable : (prefixWord ++ tailWord_347640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347640).length < 2 ^ (prefixWord ++ tailWord_347640).sum := by decide
  have hdescent : baseEnd_347640 < baseStart_347640 := by decide
  rcases family_descends (prefixWord ++ tailWord_347640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347676 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_347676 : Nat := 118140960795 + 347676 * 2 ^ 59
def prefixEnd_347676 : Nat := 4983230072969 + 3 ^ 40 * 347676 * 2
def baseEnd_347676 : Nat := 178524900032686949751073

theorem tailTrace_347676 : CollatzResearch.WordTrace tailWord_347676 prefixEnd_347676 178524900032686949751073 := by
  unfold tailWord_347676
  simp only [CollatzResearch.WordTrace]
  refine ⟨6340392744218352589279441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8453856992291136785705921 6340392744218352589279441)
  ·
    refine ⟨4755294558163764441959581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6340392744218352589279441 4755294558163764441959581)
    ·
      refine ⟨1783235459311411665734843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4755294558163764441959581 1783235459311411665734843)
      ·
        refine ⟨2674853188967117498602265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1783235459311411665734843 2674853188967117498602265)
        ·
          refine ⟨2006139891725338123951699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2674853188967117498602265 2006139891725338123951699)
          ·
            refine ⟨3009209837588007185927549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006139891725338123951699 3009209837588007185927549)
            ·
              refine ⟨1128453689095502694722831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3009209837588007185927549 1128453689095502694722831)
              ·
                refine ⟨1692680533643254042084247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128453689095502694722831 1692680533643254042084247)
                ·
                  refine ⟨2539020800464881063126371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1692680533643254042084247 2539020800464881063126371)
                  ·
                    refine ⟨3808531200697321594689557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2539020800464881063126371 3808531200697321594689557)
                    ·
                      refine ⟨178524900032686949751073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3808531200697321594689557 178524900032686949751073)
                      ·
                        rfl

theorem cell23_347676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_347676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347676 prefixEnd_347676 := by exact prefixLift 347676
  have htrace : WordTrace (prefixWord ++ tailWord_347676) baseStart_347676 baseEnd_347676 := by
    simpa [prefixWord, tailWord_347676, baseEnd_347676] using wordTrace_append hprefix tailTrace_347676
  have hstable : (prefixWord ++ tailWord_347676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347676).length < 2 ^ (prefixWord ++ tailWord_347676).sum := by decide
  have hdescent : baseEnd_347676 < baseStart_347676 := by decide
  rcases family_descends (prefixWord ++ tailWord_347676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347680 : List Nat := [2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 4]
def baseStart_347680 : Nat := 118140960795 + 347680 * 2 ^ 59
def prefixEnd_347680 : Nat := 4983230072969 + 3 ^ 40 * 347680 * 2
def baseEnd_347680 : Nat := 178526953955304934101055

theorem tailTrace_347680 : CollatzResearch.WordTrace tailWord_347680 prefixEnd_347680 178526953955304934101055 := by
  unfold tailWord_347680
  simp only [CollatzResearch.WordTrace]
  refine ⟨6340465690211106930852247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8453954253614809241136329 6340465690211106930852247)
  ·
    refine ⟨9510698535316660396278371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6340465690211106930852247 9510698535316660396278371)
    ·
      refine ⟨14266047802974990594417557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9510698535316660396278371 14266047802974990594417557)
      ·
        refine ⟨668720990764452684113323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14266047802974990594417557 668720990764452684113323)
        ·
          refine ⟨1003081486146679026169985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668720990764452684113323 1003081486146679026169985)
          ·
            refine ⟨752311114610009269627489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1003081486146679026169985 752311114610009269627489)
            ·
              refine ⟨564233335957506952220617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752311114610009269627489 564233335957506952220617)
              ·
                refine ⟨423175001968130214165463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 564233335957506952220617 423175001968130214165463)
                ·
                  refine ⟨634762502952195321248195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 423175001968130214165463 634762502952195321248195)
                  ·
                    refine ⟨952143754428292981872293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 634762502952195321248195 952143754428292981872293)
                    ·
                      refine ⟨178526953955304934101055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 952143754428292981872293 178526953955304934101055)
                      ·
                        rfl

theorem cell23_347680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_347680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347680 prefixEnd_347680 := by exact prefixLift 347680
  have htrace : WordTrace (prefixWord ++ tailWord_347680) baseStart_347680 baseEnd_347680 := by
    simpa [prefixWord, tailWord_347680, baseEnd_347680] using wordTrace_append hprefix tailTrace_347680
  have hstable : (prefixWord ++ tailWord_347680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347680).length < 2 ^ (prefixWord ++ tailWord_347680).sum := by decide
  have hdescent : baseEnd_347680 < baseStart_347680 := by decide
  rcases family_descends (prefixWord ++ tailWord_347680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347696 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 3]
def baseStart_347696 : Nat := 118140960795 + 347696 * 2 ^ 59
def prefixEnd_347696 : Nat := 4983230072969 + 3 ^ 40 * 347696 * 2
def baseEnd_347696 : Nat := 178535169645776871500981

theorem tailTrace_347696 : CollatzResearch.WordTrace tailWord_347696 prefixEnd_347696 178535169645776871500981 := by
  unfold tailWord_347696
  simp only [CollatzResearch.WordTrace]
  refine ⟨6340757474182124297143471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8454343298909499062857961 6340757474182124297143471)
  ·
    refine ⟨9511136211273186445715207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6340757474182124297143471 9511136211273186445715207)
    ·
      refine ⟨14266704316909779668572811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9511136211273186445715207 14266704316909779668572811)
      ·
        refine ⟨21400056475364669502859217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14266704316909779668572811 21400056475364669502859217)
        ·
          refine ⟨16050042356523502127144413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21400056475364669502859217 16050042356523502127144413)
          ·
            refine ⟨6018765883696313297679155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16050042356523502127144413 6018765883696313297679155)
            ·
              refine ⟨9028148825544469946518733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6018765883696313297679155 9028148825544469946518733)
              ·
                refine ⟨3385555809579176229944525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9028148825544469946518733 3385555809579176229944525)
                ·
                  refine ⟨1269583428592191086229197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3385555809579176229944525 1269583428592191086229197)
                  ·
                    refine ⟨476093785722071657335949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1269583428592191086229197 476093785722071657335949)
                    ·
                      refine ⟨178535169645776871500981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 476093785722071657335949 178535169645776871500981)
                      ·
                        rfl

theorem cell23_347696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 3].length) (baseStart_347696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347696 prefixEnd_347696 := by exact prefixLift 347696
  have htrace : WordTrace (prefixWord ++ tailWord_347696) baseStart_347696 baseEnd_347696 := by
    simpa [prefixWord, tailWord_347696, baseEnd_347696] using wordTrace_append hprefix tailTrace_347696
  have hstable : (prefixWord ++ tailWord_347696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347696).length < 2 ^ (prefixWord ++ tailWord_347696).sum := by decide
  have hdescent : baseEnd_347696 < baseStart_347696 := by decide
  rcases family_descends (prefixWord ++ tailWord_347696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347723 : List Nat := [1, 1, 1, 1, 3, 1, 3, 4, 3, 3, 2]
def baseStart_347723 : Nat := 118140960795 + 347723 * 2 ^ 59
def prefixEnd_347723 : Nat := 4983230072969 + 3 ^ 40 * 347723 * 2
def baseEnd_347723 : Nat := 178549033623448265863357

theorem tailTrace_347723 : CollatzResearch.WordTrace tailWord_347723 prefixEnd_347723 178549033623448265863357 := by
  unfold tailWord_347723
  simp only [CollatzResearch.WordTrace]
  refine ⟨12682499719266432205519823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8454999812844288137013215 12682499719266432205519823)
  ·
    refine ⟨19023749578899648308279735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12682499719266432205519823 19023749578899648308279735)
    ·
      refine ⟨28535624368349472462419603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19023749578899648308279735 28535624368349472462419603)
      ·
        refine ⟨42803436552524208693629405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28535624368349472462419603 42803436552524208693629405)
        ·
          refine ⟨16051288707196578260111027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42803436552524208693629405 16051288707196578260111027)
          ·
            refine ⟨24076933060794867390166541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16051288707196578260111027 24076933060794867390166541)
            ·
              refine ⟨9028849897798075271312453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24076933060794867390166541 9028849897798075271312453)
              ·
                refine ⟨1692909355837139113371085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9028849897798075271312453 1692909355837139113371085)
                ·
                  refine ⟨634841008438927167514157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1692909355837139113371085 634841008438927167514157)
                  ·
                    refine ⟨238065378164597687817809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 634841008438927167514157 238065378164597687817809)
                    ·
                      refine ⟨178549033623448265863357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 238065378164597687817809 178549033623448265863357)
                      ·
                        rfl

theorem cell23_347723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4, 3, 3, 2].length) (baseStart_347723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347723 prefixEnd_347723 := by exact prefixLift 347723
  have htrace : WordTrace (prefixWord ++ tailWord_347723) baseStart_347723 baseEnd_347723 := by
    simpa [prefixWord, tailWord_347723, baseEnd_347723] using wordTrace_append hprefix tailTrace_347723
  have hstable : (prefixWord ++ tailWord_347723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347723).length < 2 ^ (prefixWord ++ tailWord_347723).sum := by decide
  have hdescent : baseEnd_347723 < baseStart_347723 := by decide
  rcases family_descends (prefixWord ++ tailWord_347723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347734 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_347734 : Nat := 118140960795 + 347734 * 2 ^ 59
def prefixEnd_347734 : Nat := 4983230072969 + 3 ^ 40 * 347734 * 2
def baseEnd_347734 : Nat := 178554681910647722825807

theorem tailTrace_347734 : CollatzResearch.WordTrace tailWord_347734 prefixEnd_347734 178554681910647722825807 := by
  unfold tailWord_347734
  simp only [CollatzResearch.WordTrace]
  refine ⟨792681307639161317760641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8455267281484387389446837 792681307639161317760641)
  ·
    refine ⟨594510980729370988320481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 792681307639161317760641 594510980729370988320481)
    ·
      refine ⟨445883235547028241240361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 594510980729370988320481 445883235547028241240361)
      ·
        refine ⟨334412426660271180930271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445883235547028241240361 334412426660271180930271)
        ·
          refine ⟨501618639990406771395407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334412426660271180930271 501618639990406771395407)
          ·
            refine ⟨752427959985610157093111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501618639990406771395407 752427959985610157093111)
            ·
              refine ⟨1128641939978415235639667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752427959985610157093111 1128641939978415235639667)
              ·
                refine ⟨1692962909967622853459501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128641939978415235639667 1692962909967622853459501)
                ·
                  refine ⟨634861091237858570047313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1692962909967622853459501 634861091237858570047313)
                  ·
                    refine ⟨476145818428393927535485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 634861091237858570047313 476145818428393927535485)
                    ·
                      refine ⟨178554681910647722825807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 476145818428393927535485 178554681910647722825807)
                      ·
                        rfl

theorem cell23_347734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_347734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347734 prefixEnd_347734 := by exact prefixLift 347734
  have htrace : WordTrace (prefixWord ++ tailWord_347734) baseStart_347734 baseEnd_347734 := by
    simpa [prefixWord, tailWord_347734, baseEnd_347734] using wordTrace_append hprefix tailTrace_347734
  have hstable : (prefixWord ++ tailWord_347734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347734).length < 2 ^ (prefixWord ++ tailWord_347734).sum := by decide
  have hdescent : baseEnd_347734 < baseStart_347734 := by decide
  rcases family_descends (prefixWord ++ tailWord_347734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347753 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 3, 4, 2]
def baseStart_347753 : Nat := 118140960795 + 347753 * 2 ^ 59
def prefixEnd_347753 : Nat := 4983230072969 + 3 ^ 40 * 347753 * 2
def baseEnd_347753 : Nat := 178564438043083148488219

theorem tailTrace_347753 : CollatzResearch.WordTrace tailWord_347753 prefixEnd_347753 178564438043083148488219 := by
  unfold tailWord_347753
  simp only [CollatzResearch.WordTrace]
  refine ⟨12683593909157747329111913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8455729272771831552741275 12683593909157747329111913)
  ·
    refine ⟨9512695431868310496833935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12683593909157747329111913 9512695431868310496833935)
    ·
      refine ⟨14269043147802465745250903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9512695431868310496833935 14269043147802465745250903)
      ·
        refine ⟨21403564721703698617876355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14269043147802465745250903 21403564721703698617876355)
        ·
          refine ⟨32105347082555547926814533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21403564721703698617876355 32105347082555547926814533)
          ·
            refine ⟨6019752577979165236277725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32105347082555547926814533 6019752577979165236277725)
            ·
              refine ⟨2257407216742186963604147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6019752577979165236277725 2257407216742186963604147)
              ·
                refine ⟨3386110825113280445406221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2257407216742186963604147 3386110825113280445406221)
                ·
                  refine ⟨1269791559417480167027333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3386110825113280445406221 1269791559417480167027333)
                  ·
                    refine ⟨238085917390777531317625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1269791559417480167027333 238085917390777531317625)
                    ·
                      refine ⟨178564438043083148488219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 238085917390777531317625 178564438043083148488219)
                      ·
                        rfl

theorem cell23_347753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 4, 2].length) (baseStart_347753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347753 prefixEnd_347753 := by exact prefixLift 347753
  have htrace : WordTrace (prefixWord ++ tailWord_347753) baseStart_347753 baseEnd_347753 := by
    simpa [prefixWord, tailWord_347753, baseEnd_347753] using wordTrace_append hprefix tailTrace_347753
  have hstable : (prefixWord ++ tailWord_347753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347753).length < 2 ^ (prefixWord ++ tailWord_347753).sum := by decide
  have hdescent : baseEnd_347753 < baseStart_347753 := by decide
  rcases family_descends (prefixWord ++ tailWord_347753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347773 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 2, 4, 3]
def baseStart_347773 : Nat := 118140960795 + 347773 * 2 ^ 59
def prefixEnd_347773 : Nat := 4983230072969 + 3 ^ 40 * 347773 * 2
def baseEnd_347773 : Nat := 178574707656173070238127

theorem tailTrace_347773 : CollatzResearch.WordTrace tailWord_347773 prefixEnd_347773 178574707656173070238127 := by
  unfold tailWord_347773
  simp only [CollatzResearch.WordTrace]
  refine ⟨12684323369085290744839973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8456215579390193829893315 12684323369085290744839973)
  ·
    refine ⟨2378310631703492014657495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12684323369085290744839973 2378310631703492014657495)
    ·
      refine ⟨3567465947555238021986243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2378310631703492014657495 3567465947555238021986243)
      ·
        refine ⟨5351198921332857032979365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3567465947555238021986243 5351198921332857032979365)
        ·
          refine ⟨1003349797749910693683631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5351198921332857032979365 1003349797749910693683631)
          ·
            refine ⟨1505024696624866040525447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003349797749910693683631 1505024696624866040525447)
            ·
              refine ⟨2257537044937299060788171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505024696624866040525447 2257537044937299060788171)
              ·
                refine ⟨3386305567405948591182257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2257537044937299060788171 3386305567405948591182257)
                ·
                  refine ⟨2539729175554461443386693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3386305567405948591182257 2539729175554461443386693)
                  ·
                    refine ⟨476199220416461520635005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2539729175554461443386693 476199220416461520635005)
                    ·
                      refine ⟨178574707656173070238127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 476199220416461520635005 178574707656173070238127)
                      ·
                        rfl

theorem cell23_347773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_347773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347773 prefixEnd_347773 := by exact prefixLift 347773
  have htrace : WordTrace (prefixWord ++ tailWord_347773) baseStart_347773 baseEnd_347773 := by
    simpa [prefixWord, tailWord_347773, baseEnd_347773] using wordTrace_append hprefix tailTrace_347773
  have hstable : (prefixWord ++ tailWord_347773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347773).length < 2 ^ (prefixWord ++ tailWord_347773).sum := by decide
  have hdescent : baseEnd_347773 < baseStart_347773 := by decide
  rcases family_descends (prefixWord ++ tailWord_347773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347776 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 7]
def baseStart_347776 : Nat := 118140960795 + 347776 * 2 ^ 59
def prefixEnd_347776 : Nat := 4983230072969 + 3 ^ 40 * 347776 * 2
def baseEnd_347776 : Nat := 19841805344237395388957

theorem tailTrace_347776 : CollatzResearch.WordTrace tailWord_347776 prefixEnd_347776 19841805344237395388957 := by
  unfold tailWord_347776
  simp only [CollatzResearch.WordTrace]
  refine ⟨6342216394037211128599591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8456288525382948171466121 6342216394037211128599591)
  ·
    refine ⟨9513324591055816692899387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6342216394037211128599591 9513324591055816692899387)
    ·
      refine ⟨14269986886583725039349081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9513324591055816692899387 14269986886583725039349081)
      ·
        refine ⟨10702490164937793779511811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14269986886583725039349081 10702490164937793779511811)
        ·
          refine ⟨16053735247406690669267717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10702490164937793779511811 16053735247406690669267717)
          ·
            refine ⟨3010075358888754500487697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16053735247406690669267717 3010075358888754500487697)
            ·
              refine ⟨2257556519166565875365773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3010075358888754500487697 2257556519166565875365773)
              ·
                refine ⟨846583694687462203262165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2257556519166565875365773 846583694687462203262165)
                ·
                  refine ⟨19841805344237395388957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 846583694687462203262165 19841805344237395388957)
                  ·
                    rfl

theorem cell23_347776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 7].length) (baseStart_347776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347776 prefixEnd_347776 := by exact prefixLift 347776
  have htrace : WordTrace (prefixWord ++ tailWord_347776) baseStart_347776 baseEnd_347776 := by
    simpa [prefixWord, tailWord_347776, baseEnd_347776] using wordTrace_append hprefix tailTrace_347776
  have hstable : (prefixWord ++ tailWord_347776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347776).length < 2 ^ (prefixWord ++ tailWord_347776).sum := by decide
  have hdescent : baseEnd_347776 < baseStart_347776 := by decide
  rcases family_descends (prefixWord ++ tailWord_347776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347783 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 4]
def baseStart_347783 : Nat := 118140960795 + 347783 * 2 ^ 59
def prefixEnd_347783 : Nat := 4983230072969 + 3 ^ 40 * 347783 * 2
def baseEnd_347783 : Nat := 178579842462718031113081

theorem tailTrace_347783 : CollatzResearch.WordTrace tailWord_347783 prefixEnd_347783 178579842462718031113081 := by
  unfold tailWord_347783
  simp only [CollatzResearch.WordTrace]
  refine ⟨12684688099049062452704003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8456458732699374968469335 12684688099049062452704003)
  ·
    refine ⟨19027032148573593679056005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12684688099049062452704003 19027032148573593679056005)
    ·
      refine ⟨3567568527857548814823001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19027032148573593679056005 3567568527857548814823001)
      ·
        refine ⟨2675676395893161611117251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3567568527857548814823001 2675676395893161611117251)
        ·
          refine ⟨4013514593839742416675877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2675676395893161611117251 4013514593839742416675877)
          ·
            refine ⟨752533986344951703126727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4013514593839742416675877 752533986344951703126727)
            ·
              refine ⟨1128800979517427554690091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752533986344951703126727 1128800979517427554690091)
              ·
                refine ⟨1693201469276141332035137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128800979517427554690091 1693201469276141332035137)
                ·
                  refine ⟨1269901101957105999026353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1693201469276141332035137 1269901101957105999026353)
                  ·
                    refine ⟨952425826467829499269765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1269901101957105999026353 952425826467829499269765)
                    ·
                      refine ⟨178579842462718031113081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 952425826467829499269765 178579842462718031113081)
                      ·
                        rfl

theorem cell23_347783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_347783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347783 prefixEnd_347783 := by exact prefixLift 347783
  have htrace : WordTrace (prefixWord ++ tailWord_347783) baseStart_347783 baseEnd_347783 := by
    simpa [prefixWord, tailWord_347783, baseEnd_347783] using wordTrace_append hprefix tailTrace_347783
  have hstable : (prefixWord ++ tailWord_347783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347783).length < 2 ^ (prefixWord ++ tailWord_347783).sum := by decide
  have hdescent : baseEnd_347783 < baseStart_347783 := by decide
  rcases family_descends (prefixWord ++ tailWord_347783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347856 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 6]
def baseStart_347856 : Nat := 118140960795 + 347856 * 2 ^ 59
def prefixEnd_347856 : Nat := 4983230072969 + 3 ^ 40 * 347856 * 2
def baseEnd_347856 : Nat := 178617326550496245500245

theorem tailTrace_347856 : CollatzResearch.WordTrace tailWord_347856 prefixEnd_347856 178617326550496245500245 := by
  unfold tailWord_347856
  simp only [CollatzResearch.WordTrace]
  refine ⟨6343675313892297960055711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8458233751856397280074281 6343675313892297960055711)
  ·
    refine ⟨9515512970838446940083567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6343675313892297960055711 9515512970838446940083567)
    ·
      refine ⟨14273269456257670410125351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9515512970838446940083567 14273269456257670410125351)
      ·
        refine ⟨21409904184386505615188027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14273269456257670410125351 21409904184386505615188027)
        ·
          refine ⟨32114856276579758422782041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21409904184386505615188027 32114856276579758422782041)
          ·
            refine ⟨24086142207434818817086531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32114856276579758422782041 24086142207434818817086531)
            ·
              refine ⟨36129213311152228225629797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24086142207434818817086531 36129213311152228225629797)
              ·
                refine ⟨6774227495841042792305587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36129213311152228225629797 6774227495841042792305587)
                ·
                  refine ⟨10161341243761564188458381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6774227495841042792305587 10161341243761564188458381)
                  ·
                    refine ⟨3810502966410586570671893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10161341243761564188458381 3810502966410586570671893)
                    ·
                      refine ⟨178617326550496245500245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3810502966410586570671893 178617326550496245500245)
                      ·
                        rfl

theorem cell23_347856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_347856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347856 prefixEnd_347856 := by exact prefixLift 347856
  have htrace : WordTrace (prefixWord ++ tailWord_347856) baseStart_347856 baseEnd_347856 := by
    simpa [prefixWord, tailWord_347856, baseEnd_347856] using wordTrace_append hprefix tailTrace_347856
  have hstable : (prefixWord ++ tailWord_347856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347856).length < 2 ^ (prefixWord ++ tailWord_347856).sum := by decide
  have hdescent : baseEnd_347856 < baseStart_347856 := by decide
  rcases family_descends (prefixWord ++ tailWord_347856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347860 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 1, 3, 4]
def baseStart_347860 : Nat := 118140960795 + 347860 * 2 ^ 59
def prefixEnd_347860 : Nat := 4983230072969 + 3 ^ 40 * 347860 * 2
def baseEnd_347860 : Nat := 178619380473114229850227

theorem tailTrace_347860 : CollatzResearch.WordTrace tailWord_347860 prefixEnd_347860 178619380473114229850227 := by
  unfold tailWord_347860
  simp only [CollatzResearch.WordTrace]
  refine ⟨6343748259885052301628517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8458331013180069735504689 6343748259885052301628517)
  ·
    refine ⟨1189452798728447306555347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6343748259885052301628517 1189452798728447306555347)
    ·
      refine ⟨1784179198092670959833021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1189452798728447306555347 1784179198092670959833021)
      ·
        refine ⟨669067199284751609937383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1784179198092670959833021 669067199284751609937383)
        ·
          refine ⟨1003600798927127414906075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669067199284751609937383 1003600798927127414906075)
          ·
            refine ⟨1505401198390691122359113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003600798927127414906075 1505401198390691122359113)
            ·
              refine ⟨1129050898793018341769335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1505401198390691122359113 1129050898793018341769335)
              ·
                refine ⟨1693576348189527512654003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1129050898793018341769335 1693576348189527512654003)
                ·
                  refine ⟨2540364522284291268981005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693576348189527512654003 2540364522284291268981005)
                  ·
                    refine ⟨952636695856609225867877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2540364522284291268981005 952636695856609225867877)
                    ·
                      refine ⟨178619380473114229850227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 952636695856609225867877 178619380473114229850227)
                      ·
                        rfl

theorem cell23_347860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_347860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347860 prefixEnd_347860 := by exact prefixLift 347860
  have htrace : WordTrace (prefixWord ++ tailWord_347860) baseStart_347860 baseEnd_347860 := by
    simpa [prefixWord, tailWord_347860, baseEnd_347860] using wordTrace_append hprefix tailTrace_347860
  have hstable : (prefixWord ++ tailWord_347860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347860).length < 2 ^ (prefixWord ++ tailWord_347860).sum := by decide
  have hdescent : baseEnd_347860 < baseStart_347860 := by decide
  rcases family_descends (prefixWord ++ tailWord_347860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347863 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 3]
def baseStart_347863 : Nat := 118140960795 + 347863 * 2 ^ 59
def prefixEnd_347863 : Nat := 4983230072969 + 3 ^ 40 * 347863 * 2
def baseEnd_347863 : Nat := 178620920915077718112713

theorem tailTrace_347863 : CollatzResearch.WordTrace tailWord_347863 prefixEnd_347863 178620920915077718112713 := by
  unfold tailWord_347863
  simp only [CollatzResearch.WordTrace]
  refine ⟨12687605938759236115616243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8458403959172824077077495 12687605938759236115616243)
  ·
    refine ⟨19031408908138854173424365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12687605938759236115616243 19031408908138854173424365)
    ·
      refine ⟨7136778340552070315034137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19031408908138854173424365 7136778340552070315034137)
      ·
        refine ⟨5352583755414052736275603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7136778340552070315034137 5352583755414052736275603)
        ·
          refine ⟨8028875633121079104413405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5352583755414052736275603 8028875633121079104413405)
          ·
            refine ⟨3010828362420404664155027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8028875633121079104413405 3010828362420404664155027)
            ·
              refine ⟨4516242543630606996232541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3010828362420404664155027 4516242543630606996232541)
              ·
                refine ⟨1693590953861477623587203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4516242543630606996232541 1693590953861477623587203)
                ·
                  refine ⟨2540386430792216435380805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1693590953861477623587203 2540386430792216435380805)
                  ·
                    refine ⟨476322455773540581633901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2540386430792216435380805 476322455773540581633901)
                    ·
                      refine ⟨178620920915077718112713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 476322455773540581633901 178620920915077718112713)
                      ·
                        rfl

theorem cell23_347863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_347863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347863 prefixEnd_347863 := by exact prefixLift 347863
  have htrace : WordTrace (prefixWord ++ tailWord_347863) baseStart_347863 baseEnd_347863 := by
    simpa [prefixWord, tailWord_347863, baseEnd_347863] using wordTrace_append hprefix tailTrace_347863
  have hstable : (prefixWord ++ tailWord_347863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347863).length < 2 ^ (prefixWord ++ tailWord_347863).sum := by decide
  have hdescent : baseEnd_347863 < baseStart_347863 := by decide
  rcases family_descends (prefixWord ++ tailWord_347863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347880 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_347880 : Nat := 118140960795 + 347880 * 2 ^ 59
def prefixEnd_347880 : Nat := 4983230072969 + 3 ^ 40 * 347880 * 2
def baseEnd_347880 : Nat := 178629650086204151600135

theorem tailTrace_347880 : CollatzResearch.WordTrace tailWord_347880 prefixEnd_347880 178629650086204151600135 := by
  unfold tailWord_347880
  simp only [CollatzResearch.WordTrace]
  refine ⟨6344112989848824009492547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8458817319798432012656729 6344112989848824009492547)
  ·
    refine ⟨9516169484773236014238821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6344112989848824009492547 9516169484773236014238821)
    ·
      refine ⟨1784281778394981752669779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9516169484773236014238821 1784281778394981752669779)
      ·
        refine ⟨2676422667592472629004669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1784281778394981752669779 2676422667592472629004669)
        ·
          refine ⟨1003658500347177235876751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2676422667592472629004669 1003658500347177235876751)
          ·
            refine ⟨1505487750520765853815127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003658500347177235876751 1505487750520765853815127)
            ·
              refine ⟨2258231625781148780722691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1505487750520765853815127 2258231625781148780722691)
              ·
                refine ⟨3387347438671723171084037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2258231625781148780722691 3387347438671723171084037)
                ·
                  refine ⟨635127644750948094578257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3387347438671723171084037 635127644750948094578257)
                  ·
                    refine ⟨476345733563211070933693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 635127644750948094578257 476345733563211070933693)
                    ·
                      refine ⟨178629650086204151600135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 476345733563211070933693 178629650086204151600135)
                      ·
                        rfl

theorem cell23_347880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_347880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347880 prefixEnd_347880 := by exact prefixLift 347880
  have htrace : WordTrace (prefixWord ++ tailWord_347880) baseStart_347880 baseEnd_347880 := by
    simpa [prefixWord, tailWord_347880, baseEnd_347880] using wordTrace_append hprefix tailTrace_347880
  have hstable : (prefixWord ++ tailWord_347880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347880).length < 2 ^ (prefixWord ++ tailWord_347880).sum := by decide
  have hdescent : baseEnd_347880 < baseStart_347880 := by decide
  rcases family_descends (prefixWord ++ tailWord_347880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347937 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 2, 3, 2]
def baseStart_347937 : Nat := 118140960795 + 347937 * 2 ^ 59
def prefixEnd_347937 : Nat := 4983230072969 + 3 ^ 40 * 347937 * 2
def baseEnd_347937 : Nat := 178658918483510428587373

theorem tailTrace_347937 : CollatzResearch.WordTrace tailWord_347937 prefixEnd_347937 178658918483510428587373 := by
  unfold tailWord_347937
  simp only [CollatzResearch.WordTrace]
  refine ⟨12690304940491146753810065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8460203293660764502540043 12690304940491146753810065)
  ·
    refine ⟨9517728705368360065357549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12690304940491146753810065 9517728705368360065357549)
    ·
      refine ⟨3569148264513135024509081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9517728705368360065357549 3569148264513135024509081)
      ·
        refine ⟨2676861198384851268381811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3569148264513135024509081 2676861198384851268381811)
        ·
          refine ⟨4015291797577276902572717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676861198384851268381811 4015291797577276902572717)
          ·
            refine ⟨1505734424091478838464769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4015291797577276902572717 1505734424091478838464769)
            ·
              refine ⟨1129300818068609128848577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1505734424091478838464769 1129300818068609128848577)
              ·
                refine ⟨846975613551456846636433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129300818068609128848577 846975613551456846636433)
                ·
                  refine ⟨635231710163592634977325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 846975613551456846636433 635231710163592634977325)
                  ·
                    refine ⟨238211891311347238116497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 635231710163592634977325 238211891311347238116497)
                    ·
                      refine ⟨178658918483510428587373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 238211891311347238116497 178658918483510428587373)
                      ·
                        rfl

theorem cell23_347937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_347937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347937 prefixEnd_347937 := by exact prefixLift 347937
  have htrace : WordTrace (prefixWord ++ tailWord_347937) baseStart_347937 baseEnd_347937 := by
    simpa [prefixWord, tailWord_347937, baseEnd_347937] using wordTrace_append hprefix tailTrace_347937
  have hstable : (prefixWord ++ tailWord_347937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347937).length < 2 ^ (prefixWord ++ tailWord_347937).sum := by decide
  have hdescent : baseEnd_347937 < baseStart_347937 := by decide
  rcases family_descends (prefixWord ++ tailWord_347937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347960 : List Nat := [2, 1, 2, 1, 3, 4, 2, 1, 1, 6]
def baseStart_347960 : Nat := 118140960795 + 347960 * 2 ^ 59
def prefixEnd_347960 : Nat := 4983230072969 + 3 ^ 40 * 347960 * 2
def baseEnd_347960 : Nat := 59556909512854612866589

theorem tailTrace_347960 : CollatzResearch.WordTrace tailWord_347960 prefixEnd_347960 59556909512854612866589 := by
  unfold tailWord_347960
  simp only [CollatzResearch.WordTrace]
  refine ⟨6345571909703910840948667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8460762546271881121264889 6345571909703910840948667)
  ·
    refine ⟨9518357864555866261423001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6345571909703910840948667 9518357864555866261423001)
    ·
      refine ⟨7138768398416899696067251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9518357864555866261423001 7138768398416899696067251)
      ·
        refine ⟨10708152597625349544100877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7138768398416899696067251 10708152597625349544100877)
        ·
          refine ⟨4015557224109506079037829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10708152597625349544100877 4015557224109506079037829)
          ·
            refine ⟨752916979520532389819593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4015557224109506079037829 752916979520532389819593)
            ·
              refine ⟨564687734640399292364695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752916979520532389819593 564687734640399292364695)
              ·
                refine ⟨847031601960598938547043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564687734640399292364695 847031601960598938547043)
                ·
                  refine ⟨1270547402940898407820565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847031601960598938547043 1270547402940898407820565)
                  ·
                    refine ⟨59556909512854612866589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1270547402940898407820565 59556909512854612866589)
                    ·
                      rfl

theorem cell23_347960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_347960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347960 prefixEnd_347960 := by exact prefixLift 347960
  have htrace : WordTrace (prefixWord ++ tailWord_347960) baseStart_347960 baseEnd_347960 := by
    simpa [prefixWord, tailWord_347960, baseEnd_347960] using wordTrace_append hprefix tailTrace_347960
  have hstable : (prefixWord ++ tailWord_347960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347960).length < 2 ^ (prefixWord ++ tailWord_347960).sum := by decide
  have hdescent : baseEnd_347960 < baseStart_347960 := by decide
  rcases family_descends (prefixWord ++ tailWord_347960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347981 : List Nat := [1, 6, 1, 2, 1, 3, 2, 1, 1, 5]
def baseStart_347981 : Nat := 118140960795 + 347981 * 2 ^ 59
def prefixEnd_347981 : Nat := 4983230072969 + 3 ^ 40 * 347981 * 2
def baseEnd_347981 : Nat := 59560503877436085479057

theorem tailTrace_347981 : CollatzResearch.WordTrace tailWord_347981 prefixEnd_347981 59560503877436085479057 := by
  unfold tailWord_347981
  simp only [CollatzResearch.WordTrace]
  refine ⟨12691909752331742268411797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8461273168221161512274531 12691909752331742268411797)
  ·
    refine ⟨594933269640550418831803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12691909752331742268411797 594933269640550418831803)
    ·
      refine ⟨892399904460825628247705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 594933269640550418831803 892399904460825628247705)
      ·
        refine ⟨669299928345619221185779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 892399904460825628247705 669299928345619221185779)
        ·
          refine ⟨1003949892518428831778669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669299928345619221185779 1003949892518428831778669)
          ·
            refine ⟨376481209694410811917001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1003949892518428831778669 376481209694410811917001)
            ·
              refine ⟨282360907270808108937751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376481209694410811917001 282360907270808108937751)
              ·
                refine ⟨423541360906212163406627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282360907270808108937751 423541360906212163406627)
                ·
                  refine ⟨635312041359318245109941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 423541360906212163406627 635312041359318245109941)
                  ·
                    refine ⟨59560503877436085479057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 635312041359318245109941 59560503877436085479057)
                    ·
                      rfl

theorem cell23_347981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_347981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_347981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_347981 prefixEnd_347981 := by exact prefixLift 347981
  have htrace : WordTrace (prefixWord ++ tailWord_347981) baseStart_347981 baseEnd_347981 := by
    simpa [prefixWord, tailWord_347981, baseEnd_347981] using wordTrace_append hprefix tailTrace_347981
  have hstable : (prefixWord ++ tailWord_347981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347981).length < 2 ^ (prefixWord ++ tailWord_347981).sum := by decide
  have hdescent : baseEnd_347981 < baseStart_347981 := by decide
  rcases family_descends (prefixWord ++ tailWord_347981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348014 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 1, 2, 4]
def baseStart_348014 : Nat := 118140960795 + 348014 * 2 ^ 59
def prefixEnd_348014 : Nat := 4983230072969 + 3 ^ 40 * 348014 * 2
def baseEnd_348014 : Nat := 178698456493906627324519

theorem tailTrace_348014 : CollatzResearch.WordTrace tailWord_348014 prefixEnd_348014 178698456493906627324519 := by
  unfold tailWord_348014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1586639170151523613045387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8462075574141459269575397 1586639170151523613045387)
  ·
    refine ⟨2379958755227285419568081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1586639170151523613045387 2379958755227285419568081)
    ·
      refine ⟨1784969066420464064676061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2379958755227285419568081 1784969066420464064676061)
      ·
        refine ⟨669363399907674024253523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1784969066420464064676061 669363399907674024253523)
        ·
          refine ⟨1004045099861511036380285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669363399907674024253523 1004045099861511036380285)
          ·
            refine ⟨376516912448066638642607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1004045099861511036380285 376516912448066638642607)
            ·
              refine ⟨564775368672099957963911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376516912448066638642607 564775368672099957963911)
              ·
                refine ⟨847163053008149936945867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564775368672099957963911 847163053008149936945867)
                ·
                  refine ⟨1270744579512224905418801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847163053008149936945867 1270744579512224905418801)
                  ·
                    refine ⟨953058434634168679064101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1270744579512224905418801 953058434634168679064101)
                    ·
                      refine ⟨178698456493906627324519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 953058434634168679064101 178698456493906627324519)
                      ·
                        rfl

theorem cell23_348014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_348014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348014 prefixEnd_348014 := by exact prefixLift 348014
  have htrace : WordTrace (prefixWord ++ tailWord_348014) baseStart_348014 baseEnd_348014 := by
    simpa [prefixWord, tailWord_348014, baseEnd_348014] using wordTrace_append hprefix tailTrace_348014
  have hstable : (prefixWord ++ tailWord_348014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348014).length < 2 ^ (prefixWord ++ tailWord_348014).sum := by decide
  have hdescent : baseEnd_348014 < baseStart_348014 := by decide
  rcases family_descends (prefixWord ++ tailWord_348014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348090 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3]
def baseStart_348090 : Nat := 118140960795 + 348090 * 2 ^ 59
def prefixEnd_348090 : Nat := 4983230072969 + 3 ^ 40 * 348090 * 2
def baseEnd_348090 : Nat := 178737481023648329974169

theorem tailTrace_348090 : CollatzResearch.WordTrace tailWord_348090 prefixEnd_348090 178737481023648329974169 := by
  unfold tailWord_348090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3173971327234213471032431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8463923539291235922753149 3173971327234213471032431)
  ·
    refine ⟨4760956990851320206548647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3173971327234213471032431 4760956990851320206548647)
    ·
      refine ⟨7141435486276980309822971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4760956990851320206548647 7141435486276980309822971)
      ·
        refine ⟨10712153229415470464734457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7141435486276980309822971 10712153229415470464734457)
        ·
          refine ⟨8034114922061602848550843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10712153229415470464734457 8034114922061602848550843)
          ·
            refine ⟨12051172383092404272826265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8034114922061602848550843 12051172383092404272826265)
            ·
              refine ⟨9038379287319303204619699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12051172383092404272826265 9038379287319303204619699)
              ·
                refine ⟨13557568930978954806929549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9038379287319303204619699 13557568930978954806929549)
                ·
                  refine ⟨5084088349117108052598581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13557568930978954806929549 5084088349117108052598581)
                  ·
                    refine ⟨476633282729728879931117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5084088349117108052598581 476633282729728879931117)
                    ·
                      refine ⟨178737481023648329974169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 476633282729728879931117 178737481023648329974169)
                      ·
                        rfl

theorem cell23_348090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_348090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348090 prefixEnd_348090 := by exact prefixLift 348090
  have htrace : WordTrace (prefixWord ++ tailWord_348090) baseStart_348090 baseEnd_348090 := by
    simpa [prefixWord, tailWord_348090, baseEnd_348090] using wordTrace_append hprefix tailTrace_348090
  have hstable : (prefixWord ++ tailWord_348090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348090).length < 2 ^ (prefixWord ++ tailWord_348090).sum := by decide
  have hdescent : baseEnd_348090 < baseStart_348090 := by decide
  rcases family_descends (prefixWord ++ tailWord_348090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348120 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 1, 2, 5]
def baseStart_348120 : Nat := 118140960795 + 348120 * 2 ^ 59
def prefixEnd_348120 : Nat := 4983230072969 + 3 ^ 40 * 348120 * 2
def baseEnd_348120 : Nat := 178752885443283212599031

theorem tailTrace_348120 : CollatzResearch.WordTrace tailWord_348120 prefixEnd_348120 178752885443283212599031 := by
  unfold tailWord_348120
  simp only [CollatzResearch.WordTrace]
  refine ⟨6348489749414084503860907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8464652999218779338481209 6348489749414084503860907)
  ·
    refine ⟨9522734624121126755791361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6348489749414084503860907 9522734624121126755791361)
    ·
      refine ⟨7142050968090845066843521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9522734624121126755791361 7142050968090845066843521)
      ·
        refine ⟨5356538226068133800132641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7142050968090845066843521 5356538226068133800132641)
        ·
          refine ⟨4017403669551100350099481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5356538226068133800132641 4017403669551100350099481)
          ·
            refine ⟨3013052752163325262574611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4017403669551100350099481 3013052752163325262574611)
            ·
              refine ⟨4519579128244987893861917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3013052752163325262574611 4519579128244987893861917)
              ·
                refine ⟨1694842173091870460198219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4519579128244987893861917 1694842173091870460198219)
                ·
                  refine ⟨2542263259637805690297329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1694842173091870460198219 2542263259637805690297329)
                  ·
                    refine ⟨1906697444728354267722997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2542263259637805690297329 1906697444728354267722997)
                    ·
                      refine ⟨178752885443283212599031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1906697444728354267722997 178752885443283212599031)
                      ·
                        rfl

theorem cell23_348120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_348120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348120 prefixEnd_348120 := by exact prefixLift 348120
  have htrace : WordTrace (prefixWord ++ tailWord_348120) baseStart_348120 baseEnd_348120 := by
    simpa [prefixWord, tailWord_348120, baseEnd_348120] using wordTrace_append hprefix tailTrace_348120
  have hstable : (prefixWord ++ tailWord_348120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348120).length < 2 ^ (prefixWord ++ tailWord_348120).sum := by decide
  have hdescent : baseEnd_348120 < baseStart_348120 := by decide
  rcases family_descends (prefixWord ++ tailWord_348120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348174 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 3, 4]
def baseStart_348174 : Nat := 118140960795 + 348174 * 2 ^ 59
def prefixEnd_348174 : Nat := 4983230072969 + 3 ^ 40 * 348174 * 2
def baseEnd_348174 : Nat := 59593537799542000441261

theorem tailTrace_348174 : CollatzResearch.WordTrace tailWord_348174 prefixEnd_348174 59593537799542000441261 := by
  unfold tailWord_348174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587368630079067028773447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8465966027088357486791717 1587368630079067028773447)
  ·
    refine ⟨2381052945118600543160171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1587368630079067028773447 2381052945118600543160171)
    ·
      refine ⟨3571579417677900814740257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381052945118600543160171 3571579417677900814740257)
      ·
        refine ⟨2678684563258425611055193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3571579417677900814740257 2678684563258425611055193)
        ·
          refine ⟨2009013422443819208291395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2678684563258425611055193 2009013422443819208291395)
          ·
            refine ⟨3013520133665728812437093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009013422443819208291395 3013520133665728812437093)
            ·
              refine ⟨565035025062324152331955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3013520133665728812437093 565035025062324152331955)
              ·
                refine ⟨847552537593486228497933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565035025062324152331955 847552537593486228497933)
                ·
                  refine ⟨317832201597557335686725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 847552537593486228497933 317832201597557335686725)
                  ·
                    refine ⟨59593537799542000441261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 317832201597557335686725 59593537799542000441261)
                    ·
                      rfl

theorem cell23_348174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_348174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348174 prefixEnd_348174 := by exact prefixLift 348174
  have htrace : WordTrace (prefixWord ++ tailWord_348174) baseStart_348174 baseEnd_348174 := by
    simpa [prefixWord, tailWord_348174, baseEnd_348174] using wordTrace_append hprefix tailTrace_348174
  have hstable : (prefixWord ++ tailWord_348174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348174).length < 2 ^ (prefixWord ++ tailWord_348174).sum := by decide
  have hdescent : baseEnd_348174 < baseStart_348174 := by decide
  rcases family_descends (prefixWord ++ tailWord_348174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348224 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 4, 3, 2]
def baseStart_348224 : Nat := 118140960795 + 348224 * 2 ^ 59
def prefixEnd_348224 : Nat := 4983230072969 + 3 ^ 40 * 348224 * 2
def baseEnd_348224 : Nat := 178806287431350805698553

theorem tailTrace_348224 : CollatzResearch.WordTrace tailWord_348224 prefixEnd_348224 178806287431350805698553 := by
  unfold tailWord_348224
  simp only [CollatzResearch.WordTrace]
  refine ⟨6350386345225697384753863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8467181793634263179671817 6350386345225697384753863)
  ·
    refine ⟨9525579517838546077130795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6350386345225697384753863 9525579517838546077130795)
    ·
      refine ⟨14288369276757819115696193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9525579517838546077130795 14288369276757819115696193)
      ·
        refine ⟨10716276957568364336772145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14288369276757819115696193 10716276957568364336772145)
        ·
          refine ⟨8037207718176273252579109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10716276957568364336772145 8037207718176273252579109)
          ·
            refine ⟨1506976447158051234858583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8037207718176273252579109 1506976447158051234858583)
            ·
              refine ⟨2260464670737076852287875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1506976447158051234858583 2260464670737076852287875)
              ·
                refine ⟨3390697006105615278431813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2260464670737076852287875 3390697006105615278431813)
                ·
                  refine ⟨635755688644802864705965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3390697006105615278431813 635755688644802864705965)
                  ·
                    refine ⟨238408383241801074264737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 635755688644802864705965 238408383241801074264737)
                    ·
                      refine ⟨178806287431350805698553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 238408383241801074264737 178806287431350805698553)
                      ·
                        rfl

theorem cell23_348224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 4, 3, 2].length) (baseStart_348224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348224 prefixEnd_348224 := by exact prefixLift 348224
  have htrace : WordTrace (prefixWord ++ tailWord_348224) baseStart_348224 baseEnd_348224 := by
    simpa [prefixWord, tailWord_348224, baseEnd_348224] using wordTrace_append hprefix tailTrace_348224
  have hstable : (prefixWord ++ tailWord_348224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348224).length < 2 ^ (prefixWord ++ tailWord_348224).sum := by decide
  have hdescent : baseEnd_348224 < baseStart_348224 := by decide
  rcases family_descends (prefixWord ++ tailWord_348224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348271 : List Nat := [1, 1, 2, 1, 3, 5, 3, 1, 1, 1, 4]
def baseStart_348271 : Nat := 118140960795 + 348271 * 2 ^ 59
def prefixEnd_348271 : Nat := 4983230072969 + 3 ^ 40 * 348271 * 2
def baseEnd_348271 : Nat := 178830421022112121810837

theorem tailTrace_348271 : CollatzResearch.WordTrace tailWord_348271 prefixEnd_348271 178830421022112121810837 := by
  unfold tailWord_348271
  simp only [CollatzResearch.WordTrace]
  refine ⟨12702486921281121796468667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8468324614187414530979111 12702486921281121796468667)
  ·
    refine ⟨19053730381921682694703001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12702486921281121796468667 19053730381921682694703001)
    ·
      refine ⟨14290297786441262021027251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19053730381921682694703001 14290297786441262021027251)
      ·
        refine ⟨21435446679661893031540877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14290297786441262021027251 21435446679661893031540877)
        ·
          refine ⟨8038292504873209886827829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21435446679661893031540877 8038292504873209886827829)
          ·
            refine ⟨753589922331863426890109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8038292504873209886827829 753589922331863426890109)
            ·
              refine ⟨282596220874448785083791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 753589922331863426890109 282596220874448785083791)
              ·
                refine ⟨423894331311673177625687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282596220874448785083791 423894331311673177625687)
                ·
                  refine ⟨635841496967509766438531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 423894331311673177625687 635841496967509766438531)
                  ·
                    refine ⟨953762245451264649657797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 635841496967509766438531 953762245451264649657797)
                    ·
                      refine ⟨178830421022112121810837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 953762245451264649657797 178830421022112121810837)
                      ·
                        rfl

theorem cell23_348271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 1, 1, 4].length) (baseStart_348271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348271 prefixEnd_348271 := by exact prefixLift 348271
  have htrace : WordTrace (prefixWord ++ tailWord_348271) baseStart_348271 baseEnd_348271 := by
    simpa [prefixWord, tailWord_348271, baseEnd_348271] using wordTrace_append hprefix tailTrace_348271
  have hstable : (prefixWord ++ tailWord_348271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348271).length < 2 ^ (prefixWord ++ tailWord_348271).sum := by decide
  have hdescent : baseEnd_348271 < baseStart_348271 := by decide
  rcases family_descends (prefixWord ++ tailWord_348271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348274 : List Nat := [3, 2, 1, 2, 2, 2, 3, 1, 1, 1, 5]
def baseStart_348274 : Nat := 118140960795 + 348274 * 2 ^ 59
def prefixEnd_348274 : Nat := 4983230072969 + 3 ^ 40 * 348274 * 2
def baseEnd_348274 : Nat := 178831961464075610073323

theorem tailTrace_348274 : CollatzResearch.WordTrace tailWord_348274 prefixEnd_348274 178831961464075610073323 := by
  unfold tailWord_348274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3175649085067563327206969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8468397560180168872551917 3175649085067563327206969)
  ·
    refine ⟨2381736813800672495405227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3175649085067563327206969 2381736813800672495405227)
    ·
      refine ⟨3572605220701008743107841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381736813800672495405227 3572605220701008743107841)
      ·
        refine ⟨2679453915525756557330881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3572605220701008743107841 2679453915525756557330881)
        ·
          refine ⟨2009590436644317417998161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2679453915525756557330881 2009590436644317417998161)
          ·
            refine ⟨1507192827483238063498621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2009590436644317417998161 1507192827483238063498621)
            ·
              refine ⟨565197310306214273811983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1507192827483238063498621 565197310306214273811983)
              ·
                refine ⟨847795965459321410717975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565197310306214273811983 847795965459321410717975)
                ·
                  refine ⟨1271693948188982116076963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847795965459321410717975 1271693948188982116076963)
                  ·
                    refine ⟨1907540922283473174115445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1271693948188982116076963 1907540922283473174115445)
                    ·
                      refine ⟨178831961464075610073323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1907540922283473174115445 178831961464075610073323)
                      ·
                        rfl

theorem cell23_348274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_348274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348274 prefixEnd_348274 := by exact prefixLift 348274
  have htrace : WordTrace (prefixWord ++ tailWord_348274) baseStart_348274 baseEnd_348274 := by
    simpa [prefixWord, tailWord_348274, baseEnd_348274] using wordTrace_append hprefix tailTrace_348274
  have hstable : (prefixWord ++ tailWord_348274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348274).length < 2 ^ (prefixWord ++ tailWord_348274).sum := by decide
  have hdescent : baseEnd_348274 < baseStart_348274 := by decide
  rcases family_descends (prefixWord ++ tailWord_348274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348281 : List Nat := [1, 2, 1, 3, 4, 2, 2, 2, 2, 4]
def baseStart_348281 : Nat := 118140960795 + 348281 * 2 ^ 59
def prefixEnd_348281 : Nat := 4983230072969 + 3 ^ 40 * 348281 * 2
def baseEnd_348281 : Nat := 59611851942885694228597

theorem tailTrace_348281 : CollatzResearch.WordTrace tailWord_348281 prefixEnd_348281 59611851942885694228597 := by
  unfold tailWord_348281
  simp only [CollatzResearch.WordTrace]
  refine ⟨12702851651244893504332697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8468567767496595669555131 12702851651244893504332697)
  ·
    refine ⟨9527138738433670128249523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12702851651244893504332697 9527138738433670128249523)
    ·
      refine ⟨14290708107650505192374285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9527138738433670128249523 14290708107650505192374285)
      ·
        refine ⟨5359015540368939447140357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14290708107650505192374285 5359015540368939447140357)
        ·
          refine ⟨1004815413819176146338817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5359015540368939447140357 1004815413819176146338817)
          ·
            refine ⟨753611560364382109754113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1004815413819176146338817 753611560364382109754113)
            ·
              refine ⟨565208670273286582315585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753611560364382109754113 565208670273286582315585)
              ·
                refine ⟨423906502704964936736689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565208670273286582315585 423906502704964936736689)
                ·
                  refine ⟨317929877028723702552517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 423906502704964936736689 317929877028723702552517)
                  ·
                    refine ⟨59611851942885694228597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 317929877028723702552517 59611851942885694228597)
                    ·
                      rfl

theorem cell23_348281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 4].length) (baseStart_348281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348281 prefixEnd_348281 := by exact prefixLift 348281
  have htrace : WordTrace (prefixWord ++ tailWord_348281) baseStart_348281 baseEnd_348281 := by
    simpa [prefixWord, tailWord_348281, baseEnd_348281] using wordTrace_append hprefix tailTrace_348281
  have hstable : (prefixWord ++ tailWord_348281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348281).length < 2 ^ (prefixWord ++ tailWord_348281).sum := by decide
  have hdescent : baseEnd_348281 < baseStart_348281 := by decide
  rcases family_descends (prefixWord ++ tailWord_348281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348304 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 3]
def baseStart_348304 : Nat := 118140960795 + 348304 * 2 ^ 59
def prefixEnd_348304 : Nat := 4983230072969 + 3 ^ 40 * 348304 * 2
def baseEnd_348304 : Nat := 178847365883710492698185

theorem tailTrace_348304 : CollatzResearch.WordTrace tailWord_348304 prefixEnd_348304 178847365883710492698185 := by
  unfold tailWord_348304
  simp only [CollatzResearch.WordTrace]
  refine ⟨6351845265080784216209983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8469127020107712288279977 6351845265080784216209983)
  ·
    refine ⟨9527767897621176324314975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6351845265080784216209983 9527767897621176324314975)
    ·
      refine ⟨14291651846431764486472463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9527767897621176324314975 14291651846431764486472463)
      ·
        refine ⟨21437477769647646729708695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14291651846431764486472463 21437477769647646729708695)
        ·
          refine ⟨32156216654471470094563043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21437477769647646729708695 32156216654471470094563043)
          ·
            refine ⟨48234324981707205141844565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32156216654471470094563043 48234324981707205141844565)
            ·
              refine ⟨565245995879381310255991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 48234324981707205141844565 565245995879381310255991)
              ·
                refine ⟨847868993819071965383987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565245995879381310255991 847868993819071965383987)
                ·
                  refine ⟨1271803490728607948075981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 847868993819071965383987 1271803490728607948075981)
                  ·
                    refine ⟨476926309023227980528493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1271803490728607948075981 476926309023227980528493)
                    ·
                      refine ⟨178847365883710492698185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 476926309023227980528493 178847365883710492698185)
                      ·
                        rfl

theorem cell23_348304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 3].length) (baseStart_348304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348304 prefixEnd_348304 := by exact prefixLift 348304
  have htrace : WordTrace (prefixWord ++ tailWord_348304) baseStart_348304 baseEnd_348304 := by
    simpa [prefixWord, tailWord_348304, baseEnd_348304] using wordTrace_append hprefix tailTrace_348304
  have hstable : (prefixWord ++ tailWord_348304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348304).length < 2 ^ (prefixWord ++ tailWord_348304).sum := by decide
  have hdescent : baseEnd_348304 < baseStart_348304 := by decide
  rcases family_descends (prefixWord ++ tailWord_348304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348322 : List Nat := [3, 3, 1, 3, 1, 2, 2, 3, 1, 2, 2]
def baseStart_348322 : Nat := 118140960795 + 348322 * 2 ^ 59
def prefixEnd_348322 : Nat := 4983230072969 + 3 ^ 40 * 348322 * 2
def baseEnd_348322 : Nat := 178856608535491422273103

theorem tailTrace_348322 : CollatzResearch.WordTrace tailWord_348322 prefixEnd_348322 178856608535491422273103 := by
  unfold tailWord_348322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3176086761024089376643805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8469564696064238337716813 3176086761024089376643805)
  ·
    refine ⟨1191032535384033516241427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3176086761024089376643805 1191032535384033516241427)
    ·
      refine ⟨1786548803076050274362141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1191032535384033516241427 1786548803076050274362141)
      ·
        refine ⟨669955801153518852885803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1786548803076050274362141 669955801153518852885803)
        ·
          refine ⟨1004933701730278279328705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669955801153518852885803 1004933701730278279328705)
          ·
            refine ⟨753700276297708709496529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1004933701730278279328705 753700276297708709496529)
            ·
              refine ⟨565275207223281532122397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753700276297708709496529 565275207223281532122397)
              ·
                refine ⟨211978202708730574545899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 565275207223281532122397 211978202708730574545899)
                ·
                  refine ⟨317967304063095861818849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211978202708730574545899 317967304063095861818849)
                  ·
                    refine ⟨238475478047321896364137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 317967304063095861818849 238475478047321896364137)
                    ·
                      refine ⟨178856608535491422273103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 238475478047321896364137 178856608535491422273103)
                      ·
                        rfl

theorem cell23_348322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_348322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348322 prefixEnd_348322 := by exact prefixLift 348322
  have htrace : WordTrace (prefixWord ++ tailWord_348322) baseStart_348322 baseEnd_348322 := by
    simpa [prefixWord, tailWord_348322, baseEnd_348322] using wordTrace_append hprefix tailTrace_348322
  have hstable : (prefixWord ++ tailWord_348322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348322).length < 2 ^ (prefixWord ++ tailWord_348322).sum := by decide
  have hdescent : baseEnd_348322 < baseStart_348322 := by decide
  rcases family_descends (prefixWord ++ tailWord_348322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348367 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 7]
def baseStart_348367 : Nat := 118140960795 + 348367 * 2 ^ 59
def prefixEnd_348367 : Nat := 4983230072969 + 3 ^ 40 * 348367 * 2
def baseEnd_348367 : Nat := 19875523907215971801155

theorem tailTrace_348367 : CollatzResearch.WordTrace tailWord_348367 prefixEnd_348367 19875523907215971801155 := by
  unfold tailWord_348367
  simp only [CollatzResearch.WordTrace]
  refine ⟨12705988328933330191963355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8470658885955553461308903 12705988328933330191963355)
  ·
    refine ⟨19058982493399995287945033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12705988328933330191963355 19058982493399995287945033)
    ·
      refine ⟨14294236870049996465958775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19058982493399995287945033 14294236870049996465958775)
      ·
        refine ⟨21441355305074994698938163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14294236870049996465958775 21441355305074994698938163)
        ·
          refine ⟨32162032957612492048407245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21441355305074994698938163 32162032957612492048407245)
          ·
            refine ⟨12060762359104684518152717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32162032957612492048407245 12060762359104684518152717)
            ·
              refine ⟨4522785884664256694307269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12060762359104684518152717 4522785884664256694307269)
              ·
                refine ⟨848022353374548130182613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4522785884664256694307269 848022353374548130182613)
                ·
                  refine ⟨19875523907215971801155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 848022353374548130182613 19875523907215971801155)
                  ·
                    rfl

theorem cell23_348367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 7].length) (baseStart_348367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348367 prefixEnd_348367 := by exact prefixLift 348367
  have htrace : WordTrace (prefixWord ++ tailWord_348367) baseStart_348367 baseEnd_348367 := by
    simpa [prefixWord, tailWord_348367, baseEnd_348367] using wordTrace_append hprefix tailTrace_348367
  have hstable : (prefixWord ++ tailWord_348367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348367).length < 2 ^ (prefixWord ++ tailWord_348367).sum := by decide
  have hdescent : baseEnd_348367 < baseStart_348367 := by decide
  rcases family_descends (prefixWord ++ tailWord_348367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348381 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_348381 : Nat := 118140960795 + 348381 * 2 ^ 59
def prefixEnd_348381 : Nat := 4983230072969 + 3 ^ 40 * 348381 * 2
def baseEnd_348381 : Nat := 178886903894106691435331

theorem tailTrace_348381 : CollatzResearch.WordTrace tailWord_348381 prefixEnd_348381 178886903894106691435331 := by
  unfold tailWord_348381
  simp only [CollatzResearch.WordTrace]
  refine ⟨12706498950882610582972997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8470999300588407055315331 12706498950882610582972997)
  ·
    refine ⟨2382468553290489484307437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12706498950882610582972997 2382468553290489484307437)
    ·
      refine ⟨893425707483933556615289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2382468553290489484307437 893425707483933556615289)
      ·
        refine ⟨670069280612950167461467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 893425707483933556615289 670069280612950167461467)
        ·
          refine ⟨1005103920919425251192201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670069280612950167461467 1005103920919425251192201)
          ·
            refine ⟨753827940689568938394151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1005103920919425251192201 753827940689568938394151)
            ·
              refine ⟨1130741911034353407591227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753827940689568938394151 1130741911034353407591227)
              ·
                refine ⟨1696112866551530111386841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1130741911034353407591227 1696112866551530111386841)
                ·
                  refine ⟨1272084649913647583540131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1696112866551530111386841 1272084649913647583540131)
                  ·
                    refine ⟨1908126974870471375310197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1272084649913647583540131 1908126974870471375310197)
                    ·
                      refine ⟨178886903894106691435331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1908126974870471375310197 178886903894106691435331)
                      ·
                        rfl

theorem cell23_348381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_348381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348381 prefixEnd_348381 := by exact prefixLift 348381
  have htrace : WordTrace (prefixWord ++ tailWord_348381) baseStart_348381 baseEnd_348381 := by
    simpa [prefixWord, tailWord_348381, baseEnd_348381] using wordTrace_append hprefix tailTrace_348381
  have hstable : (prefixWord ++ tailWord_348381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348381).length < 2 ^ (prefixWord ++ tailWord_348381).sum := by decide
  have hdescent : baseEnd_348381 < baseStart_348381 := by decide
  rcases family_descends (prefixWord ++ tailWord_348381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348412 : List Nat := [2, 2, 2, 1, 4, 3, 2, 1, 2, 2, 2]
def baseStart_348412 : Nat := 118140960795 + 348412 * 2 ^ 59
def prefixEnd_348412 : Nat := 4983230072969 + 3 ^ 40 * 348412 * 2
def baseEnd_348412 : Nat := 178902821794396070147689

theorem tailTrace_348412 : CollatzResearch.WordTrace tailWord_348412 prefixEnd_348412 178902821794396070147689 := by
  unfold tailWord_348412
  simp only [CollatzResearch.WordTrace]
  refine ⟨6353814806885151438675745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8471753075846868584900993 6353814806885151438675745)
  ·
    refine ⟨4765361105163863579006809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6353814806885151438675745 4765361105163863579006809)
    ·
      refine ⟨3574020828872897684255107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4765361105163863579006809 3574020828872897684255107)
      ·
        refine ⟨5361031243309346526382661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3574020828872897684255107 5361031243309346526382661)
        ·
          refine ⟨1005193358120502473696749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5361031243309346526382661 1005193358120502473696749)
          ·
            refine ⟨376947509295188427636281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1005193358120502473696749 376947509295188427636281)
            ·
              refine ⟨282710631971391320727211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376947509295188427636281 282710631971391320727211)
              ·
                refine ⟨424065947957086981090817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282710631971391320727211 424065947957086981090817)
                ·
                  refine ⟨318049460967815235818113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 424065947957086981090817 318049460967815235818113)
                  ·
                    refine ⟨238537095725861426863585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 318049460967815235818113 238537095725861426863585)
                    ·
                      refine ⟨178902821794396070147689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 238537095725861426863585 178902821794396070147689)
                      ·
                        rfl

theorem cell23_348412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 2, 2, 2].length) (baseStart_348412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348412 prefixEnd_348412 := by exact prefixLift 348412
  have htrace : WordTrace (prefixWord ++ tailWord_348412) baseStart_348412 baseEnd_348412 := by
    simpa [prefixWord, tailWord_348412, baseEnd_348412] using wordTrace_append hprefix tailTrace_348412
  have hstable : (prefixWord ++ tailWord_348412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348412).length < 2 ^ (prefixWord ++ tailWord_348412).sum := by decide
  have hdescent : baseEnd_348412 < baseStart_348412 := by decide
  rcases family_descends (prefixWord ++ tailWord_348412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348451 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 2, 4, 2]
def baseStart_348451 : Nat := 118140960795 + 348451 * 2 ^ 59
def prefixEnd_348451 : Nat := 4983230072969 + 3 ^ 40 * 348451 * 2
def baseEnd_348451 : Nat := 178922847539921417560009

theorem tailTrace_348451 : CollatzResearch.WordTrace tailWord_348451 prefixEnd_348451 178922847539921417560009 := by
  unfold tailWord_348451
  simp only [CollatzResearch.WordTrace]
  refine ⟨12709052060629012538021207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8472701373752675025347471 12709052060629012538021207)
  ·
    refine ⟨19063578090943518807031811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12709052060629012538021207 19063578090943518807031811)
    ·
      refine ⟨28595367136415278210547717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19063578090943518807031811 28595367136415278210547717)
      ·
        refine ⟨5361631338077864664477697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28595367136415278210547717 5361631338077864664477697)
        ·
          refine ⟨4021223503558398498358273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5361631338077864664477697 4021223503558398498358273)
          ·
            refine ⟨3015917627668798873768705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4021223503558398498358273 3015917627668798873768705)
            ·
              refine ⟨2261938220751599155326529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3015917627668798873768705 2261938220751599155326529)
              ·
                refine ⟨1696453665563699366494897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2261938220751599155326529 1696453665563699366494897)
                ·
                  refine ⟨1272340249172774524871173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1696453665563699366494897 1272340249172774524871173)
                  ·
                    refine ⟨238563796719895223413345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1272340249172774524871173 238563796719895223413345)
                    ·
                      refine ⟨178922847539921417560009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 238563796719895223413345 178922847539921417560009)
                      ·
                        rfl

theorem cell23_348451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_348451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348451 prefixEnd_348451 := by exact prefixLift 348451
  have htrace : WordTrace (prefixWord ++ tailWord_348451) baseStart_348451 baseEnd_348451 := by
    simpa [prefixWord, tailWord_348451, baseEnd_348451] using wordTrace_append hprefix tailTrace_348451
  have hstable : (prefixWord ++ tailWord_348451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348451).length < 2 ^ (prefixWord ++ tailWord_348451).sum := by decide
  have hdescent : baseEnd_348451 < baseStart_348451 := by decide
  rcases family_descends (prefixWord ++ tailWord_348451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348468 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_348468 : Nat := 118140960795 + 348468 * 2 ^ 59
def prefixEnd_348468 : Nat := 4983230072969 + 3 ^ 40 * 348468 * 2
def baseEnd_348468 : Nat := 178931576711047851047431

theorem tailTrace_348468 : CollatzResearch.WordTrace tailWord_348468 prefixEnd_348468 178931576711047851047431 := by
  unfold tailWord_348468
  simp only [CollatzResearch.WordTrace]
  refine ⟨6354836050783712220695029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8473114734378282960926705 6354836050783712220695029)
  ·
    refine ⟨595765879760973020690159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6354836050783712220695029 595765879760973020690159)
    ·
      refine ⟨893648819641459531035239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 595765879760973020690159 893648819641459531035239)
      ·
        refine ⟨1340473229462189296552859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893648819641459531035239 1340473229462189296552859)
        ·
          refine ⟨2010709844193283944829289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1340473229462189296552859 2010709844193283944829289)
          ·
            refine ⟨1508032383144962958621967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2010709844193283944829289 1508032383144962958621967)
            ·
              refine ⟨2262048574717444437932951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1508032383144962958621967 2262048574717444437932951)
              ·
                refine ⟨3393072862076166656899427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2262048574717444437932951 3393072862076166656899427)
                ·
                  refine ⟨5089609293114249985349141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3393072862076166656899427 5089609293114249985349141)
                  ·
                    refine ⟨238575435614730468063241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5089609293114249985349141 238575435614730468063241)
                    ·
                      refine ⟨178931576711047851047431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 238575435614730468063241 178931576711047851047431)
                      ·
                        rfl

theorem cell23_348468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_348468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348468 prefixEnd_348468 := by exact prefixLift 348468
  have htrace : WordTrace (prefixWord ++ tailWord_348468) baseStart_348468 baseEnd_348468 := by
    simpa [prefixWord, tailWord_348468, baseEnd_348468] using wordTrace_append hprefix tailTrace_348468
  have hstable : (prefixWord ++ tailWord_348468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348468).length < 2 ^ (prefixWord ++ tailWord_348468).sum := by decide
  have hdescent : baseEnd_348468 < baseStart_348468 := by decide
  rcases family_descends (prefixWord ++ tailWord_348468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348478 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_348478 : Nat := 118140960795 + 348478 * 2 ^ 59
def prefixEnd_348478 : Nat := 4983230072969 + 3 ^ 40 * 348478 * 2
def baseEnd_348478 : Nat := 59645570505864270640795

theorem tailTrace_348478 : CollatzResearch.WordTrace tailWord_348478 prefixEnd_348478 59645570505864270640795 := by
  unfold tailWord_348478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1588754603941399518656761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8473357887687464099502725 1588754603941399518656761)
  ·
    refine ⟨1191565952956049638992571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1588754603941399518656761 1191565952956049638992571)
    ·
      refine ⟨1787348929434074458488857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1191565952956049638992571 1787348929434074458488857)
      ·
        refine ⟨1340511697075555843866643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1787348929434074458488857 1340511697075555843866643)
        ·
          refine ⟨2010767545613333765799965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1340511697075555843866643 2010767545613333765799965)
          ·
            refine ⟨754037829605000162174987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2010767545613333765799965 754037829605000162174987)
            ·
              refine ⟨1131056744407500243262481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754037829605000162174987 1131056744407500243262481)
              ·
                refine ⟨848292558305625182446861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1131056744407500243262481 848292558305625182446861)
                ·
                  refine ⟨318109709364609443417573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 848292558305625182446861 318109709364609443417573)
                  ·
                    refine ⟨59645570505864270640795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 318109709364609443417573 59645570505864270640795)
                    ·
                      rfl

theorem cell23_348478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_348478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348478 prefixEnd_348478 := by exact prefixLift 348478
  have htrace : WordTrace (prefixWord ++ tailWord_348478) baseStart_348478 baseEnd_348478 := by
    simpa [prefixWord, tailWord_348478, baseEnd_348478] using wordTrace_append hprefix tailTrace_348478
  have hstable : (prefixWord ++ tailWord_348478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348478).length < 2 ^ (prefixWord ++ tailWord_348478).sum := by decide
  have hdescent : baseEnd_348478 < baseStart_348478 := by decide
  rcases family_descends (prefixWord ++ tailWord_348478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348504 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 5, 5]
def baseStart_348504 : Nat := 118140960795 + 348504 * 2 ^ 59
def prefixEnd_348504 : Nat := 4983230072969 + 3 ^ 40 * 348504 * 2
def baseEnd_348504 : Nat := 59650020671536570065755

theorem tailTrace_348504 : CollatzResearch.WordTrace tailWord_348504 prefixEnd_348504 59650020671536570065755 := by
  unfold tailWord_348504
  simp only [CollatzResearch.WordTrace]
  refine ⟨6355492564718501294850283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8473990086291335059800377 6355492564718501294850283)
  ·
    refine ⟨9533238847077751942275425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6355492564718501294850283 9533238847077751942275425)
    ·
      refine ⟨7149929135308313956706569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9533238847077751942275425 7149929135308313956706569)
      ·
        refine ⟨5362446851481235467529927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7149929135308313956706569 5362446851481235467529927)
        ·
          refine ⟨8043670277221853201294891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5362446851481235467529927 8043670277221853201294891)
          ·
            refine ⟨12065505415832779801942337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8043670277221853201294891 12065505415832779801942337)
            ·
              refine ⟨9049129061874584851456753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12065505415832779801942337 9049129061874584851456753)
              ·
                refine ⟨6786846796405938638592565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9049129061874584851456753 6786846796405938638592565)
                ·
                  refine ⟨636266887163056747368053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6786846796405938638592565 636266887163056747368053)
                  ·
                    refine ⟨59650020671536570065755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 636266887163056747368053 59650020671536570065755)
                    ·
                      rfl

theorem cell23_348504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_348504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348504 prefixEnd_348504 := by exact prefixLift 348504
  have htrace : WordTrace (prefixWord ++ tailWord_348504) baseStart_348504 baseEnd_348504 := by
    simpa [prefixWord, tailWord_348504, baseEnd_348504] using wordTrace_append hprefix tailTrace_348504
  have hstable : (prefixWord ++ tailWord_348504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348504).length < 2 ^ (prefixWord ++ tailWord_348504).sum := by decide
  have hdescent : baseEnd_348504 < baseStart_348504 := by decide
  rcases family_descends (prefixWord ++ tailWord_348504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348508 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 8]
def baseStart_348508 : Nat := 118140960795 + 348508 * 2 ^ 59
def prefixEnd_348508 : Nat := 4983230072969 + 3 ^ 40 * 348508 * 2
def baseEnd_348508 : Nat := 19883568437469743838583

theorem tailTrace_348508 : CollatzResearch.WordTrace tailWord_348508 prefixEnd_348508 19883568437469743838583 := by
  unfold tailWord_348508
  simp only [CollatzResearch.WordTrace]
  refine ⟨6355565510711255636423089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8474087347615007515230785 6355565510711255636423089)
  ·
    refine ⟨4766674133033441727317317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6355565510711255636423089 4766674133033441727317317)
    ·
      refine ⟨893751399943770323871997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4766674133033441727317317 893751399943770323871997)
      ·
        refine ⟨335156774978913871451999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 893751399943770323871997 335156774978913871451999)
        ·
          refine ⟨502735162468370807177999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335156774978913871451999 502735162468370807177999)
          ·
            refine ⟨754102743702556210766999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502735162468370807177999 754102743702556210766999)
            ·
              refine ⟨1131154115553834316150499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754102743702556210766999 1131154115553834316150499)
              ·
                refine ⟨1696731173330751474225749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131154115553834316150499 1696731173330751474225749)
                ·
                  refine ⟨19883568437469743838583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1696731173330751474225749 19883568437469743838583)
                  ·
                    rfl

theorem cell23_348508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 8].length) (baseStart_348508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348508 prefixEnd_348508 := by exact prefixLift 348508
  have htrace : WordTrace (prefixWord ++ tailWord_348508) baseStart_348508 baseEnd_348508 := by
    simpa [prefixWord, tailWord_348508, baseEnd_348508] using wordTrace_append hprefix tailTrace_348508
  have hstable : (prefixWord ++ tailWord_348508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348508).length < 2 ^ (prefixWord ++ tailWord_348508).sum := by decide
  have hdescent : baseEnd_348508 < baseStart_348508 := by decide
  rcases family_descends (prefixWord ++ tailWord_348508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348546 : List Nat := [3, 4, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_348546 : Nat := 118140960795 + 348546 * 2 ^ 59
def prefixEnd_348546 : Nat := 4983230072969 + 3 ^ 40 * 348546 * 2
def baseEnd_348546 : Nat := 59657209400699515290691

theorem tailTrace_348546 : CollatzResearch.WordTrace tailWord_348546 prefixEnd_348546 59657209400699515290691 := by
  unfold tailWord_348546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3178129248821210940682373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8475011330189895841819661 3178129248821210940682373)
  ·
    refine ⟨595899234153977051377945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3178129248821210940682373 595899234153977051377945)
    ·
      refine ⟨446924425615482788533459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 595899234153977051377945 446924425615482788533459)
      ·
        refine ⟨670386638423224182800189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446924425615482788533459 670386638423224182800189)
        ·
          refine ⟨251394989408709068550071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 670386638423224182800189 251394989408709068550071)
          ·
            refine ⟨377092484113063602825107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251394989408709068550071 377092484113063602825107)
            ·
              refine ⟨565638726169595404237661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377092484113063602825107 565638726169595404237661)
              ·
                refine ⟨212114522313598276589123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 565638726169595404237661 212114522313598276589123)
                ·
                  refine ⟨318171783470397414883685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212114522313598276589123 318171783470397414883685)
                  ·
                    refine ⟨59657209400699515290691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 318171783470397414883685 59657209400699515290691)
                    ·
                      rfl

theorem cell23_348546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_348546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348546 prefixEnd_348546 := by exact prefixLift 348546
  have htrace : WordTrace (prefixWord ++ tailWord_348546) baseStart_348546 baseEnd_348546 := by
    simpa [prefixWord, tailWord_348546, baseEnd_348546] using wordTrace_append hprefix tailTrace_348546
  have hstable : (prefixWord ++ tailWord_348546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348546).length < 2 ^ (prefixWord ++ tailWord_348546).sum := by decide
  have hdescent : baseEnd_348546 < baseStart_348546 := by decide
  rcases family_descends (prefixWord ++ tailWord_348546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348551 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 6, 4]
def baseStart_348551 : Nat := 118140960795 + 348551 * 2 ^ 59
def prefixEnd_348551 : Nat := 4983230072969 + 3 ^ 40 * 348551 * 2
def baseEnd_348551 : Nat := 59658065201790342103183

theorem tailTrace_348551 : CollatzResearch.WordTrace tailWord_348551 prefixEnd_348551 59658065201790342103183 := by
  unfold tailWord_348551
  simp only [CollatzResearch.WordTrace]
  refine ⟨12712699360266729616661507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8475132906844486411107671 12712699360266729616661507)
  ·
    refine ⟨19069049040400094424992261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12712699360266729616661507 19069049040400094424992261)
    ·
      refine ⟨3575446695075017704686049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19069049040400094424992261 3575446695075017704686049)
      ·
        refine ⟨2681585021306263278514537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3575446695075017704686049 2681585021306263278514537)
        ·
          refine ⟨2011188765979697458885903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2681585021306263278514537 2011188765979697458885903)
          ·
            refine ⟨3016783148969546188328855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011188765979697458885903 3016783148969546188328855)
            ·
              refine ⟨4525174723454319282493283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3016783148969546188328855 4525174723454319282493283)
              ·
                refine ⟨6787762085181478923739925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4525174723454319282493283 6787762085181478923739925)
                ·
                  refine ⟨318176347742881824550309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6787762085181478923739925 318176347742881824550309)
                  ·
                    refine ⟨59658065201790342103183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 318176347742881824550309 59658065201790342103183)
                    ·
                      rfl

theorem cell23_348551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_348551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348551 prefixEnd_348551 := by exact prefixLift 348551
  have htrace : WordTrace (prefixWord ++ tailWord_348551) baseStart_348551 baseEnd_348551 := by
    simpa [prefixWord, tailWord_348551, baseEnd_348551] using wordTrace_append hprefix tailTrace_348551
  have hstable : (prefixWord ++ tailWord_348551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348551).length < 2 ^ (prefixWord ++ tailWord_348551).sum := by decide
  have hdescent : baseEnd_348551 < baseStart_348551 := by decide
  rcases family_descends (prefixWord ++ tailWord_348551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348568 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 4, 4]
def baseStart_348568 : Nat := 118140960795 + 348568 * 2 ^ 59
def prefixEnd_348568 : Nat := 4983230072969 + 3 ^ 40 * 348568 * 2
def baseEnd_348568 : Nat := 59660974925499153265657

theorem tailTrace_348568 : CollatzResearch.WordTrace tailWord_348568 prefixEnd_348568 59660974925499153265657 := by
  unfold tailWord_348568
  simp only [CollatzResearch.WordTrace]
  refine ⟨6356659700602570760015179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8475546267470094346686905 6356659700602570760015179)
  ·
    refine ⟨9534989550903856140022769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6356659700602570760015179 9534989550903856140022769)
    ·
      refine ⟨7151242163177892105017077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9534989550903856140022769 7151242163177892105017077)
      ·
        refine ⟨670428952797927384845351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7151242163177892105017077 670428952797927384845351)
        ·
          refine ⟨1005643429196891077268027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670428952797927384845351 1005643429196891077268027)
          ·
            refine ⟨1508465143795336615902041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005643429196891077268027 1508465143795336615902041)
            ·
              refine ⟨1131348857846502461926531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1508465143795336615902041 1131348857846502461926531)
              ·
                refine ⟨1697023286769753692889797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131348857846502461926531 1697023286769753692889797)
                ·
                  refine ⟨318191866269328817416837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1697023286769753692889797 318191866269328817416837)
                  ·
                    refine ⟨59660974925499153265657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 318191866269328817416837 59660974925499153265657)
                    ·
                      rfl

theorem cell23_348568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_348568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348568 prefixEnd_348568 := by exact prefixLift 348568
  have htrace : WordTrace (prefixWord ++ tailWord_348568) baseStart_348568 baseEnd_348568 := by
    simpa [prefixWord, tailWord_348568, baseEnd_348568] using wordTrace_append hprefix tailTrace_348568
  have hstable : (prefixWord ++ tailWord_348568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348568).length < 2 ^ (prefixWord ++ tailWord_348568).sum := by decide
  have hdescent : baseEnd_348568 < baseStart_348568 := by decide
  rcases family_descends (prefixWord ++ tailWord_348568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348578 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_348578 : Nat := 118140960795 + 348578 * 2 ^ 59
def prefixEnd_348578 : Nat := 4983230072969 + 3 ^ 40 * 348578 * 2
def baseEnd_348578 : Nat := 178988059583042420671925

theorem tailTrace_348578 : CollatzResearch.WordTrace tailWord_348578 prefixEnd_348578 178988059583042420671925 := by
  unfold tailWord_348578
  simp only [CollatzResearch.WordTrace]
  refine ⟨3178421032792228306973597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8475789420779275485262925 3178421032792228306973597)
  ·
    refine ⟨1191907887297085615115099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3178421032792228306973597 1191907887297085615115099)
    ·
      refine ⟨1787861830945628422672649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1191907887297085615115099 1787861830945628422672649)
      ·
        refine ⟨1340896373209221317004487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1787861830945628422672649 1340896373209221317004487)
        ·
          refine ⟨2011344559813831975506731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1340896373209221317004487 2011344559813831975506731)
          ·
            refine ⟨3017016839720747963260097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011344559813831975506731 3017016839720747963260097)
            ·
              refine ⟨2262762629790560972445073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3017016839720747963260097 2262762629790560972445073)
              ·
                refine ⟨1697071972342920729333805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2262762629790560972445073 1697071972342920729333805)
                ·
                  refine ⟨636401989628595273500177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1697071972342920729333805 636401989628595273500177)
                  ·
                    refine ⟨477301492221446455125133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 636401989628595273500177 477301492221446455125133)
                    ·
                      refine ⟨178988059583042420671925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 477301492221446455125133 178988059583042420671925)
                      ·
                        rfl

theorem cell23_348578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_348578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348578 prefixEnd_348578 := by exact prefixLift 348578
  have htrace : WordTrace (prefixWord ++ tailWord_348578) baseStart_348578 baseEnd_348578 := by
    simpa [prefixWord, tailWord_348578, baseEnd_348578] using wordTrace_append hprefix tailTrace_348578
  have hstable : (prefixWord ++ tailWord_348578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348578).length < 2 ^ (prefixWord ++ tailWord_348578).sum := by decide
  have hdescent : baseEnd_348578 < baseStart_348578 := by decide
  rcases family_descends (prefixWord ++ tailWord_348578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348612 : List Nat := [2, 3, 3, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_348612 : Nat := 118140960795 + 348612 * 2 ^ 59
def prefixEnd_348612 : Nat := 4983230072969 + 3 ^ 40 * 348612 * 2
def baseEnd_348612 : Nat := 179005517925295287646769

theorem tailTrace_348612 : CollatzResearch.WordTrace tailWord_348612 prefixEnd_348612 179005517925295287646769 := by
  unfold tailWord_348612
  simp only [CollatzResearch.WordTrace]
  refine ⟨6357462106522868517316045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8476616142030491356421393 6357462106522868517316045)
  ·
    refine ⟨2384048289946075693993517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6357462106522868517316045 2384048289946075693993517)
    ·
      refine ⟨894018108729778385247569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2384048289946075693993517 894018108729778385247569)
      ·
        refine ⟨670513581547333788935677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 894018108729778385247569 670513581547333788935677)
        ·
          refine ⟨251442593080250170850879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 670513581547333788935677 251442593080250170850879)
          ·
            refine ⟨377163889620375256276319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251442593080250170850879 377163889620375256276319)
            ·
              refine ⟨565745834430562884414479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377163889620375256276319 565745834430562884414479)
              ·
                refine ⟨848618751645844326621719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565745834430562884414479 848618751645844326621719)
                ·
                  refine ⟨1272928127468766489932579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 848618751645844326621719 1272928127468766489932579)
                  ·
                    refine ⟨1909392191203149734898869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1272928127468766489932579 1909392191203149734898869)
                    ·
                      refine ⟨179005517925295287646769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1909392191203149734898869 179005517925295287646769)
                      ·
                        rfl

theorem cell23_348612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_348612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348612 prefixEnd_348612 := by exact prefixLift 348612
  have htrace : WordTrace (prefixWord ++ tailWord_348612) baseStart_348612 baseEnd_348612 := by
    simpa [prefixWord, tailWord_348612, baseEnd_348612] using wordTrace_append hprefix tailTrace_348612
  have hstable : (prefixWord ++ tailWord_348612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348612).length < 2 ^ (prefixWord ++ tailWord_348612).sum := by decide
  have hdescent : baseEnd_348612 < baseStart_348612 := by decide
  rcases family_descends (prefixWord ++ tailWord_348612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348626 : List Nat := [3, 2, 2, 4, 1, 1, 1, 4, 1, 2, 2]
def baseStart_348626 : Nat := 118140960795 + 348626 * 2 ^ 59
def prefixEnd_348626 : Nat := 4983230072969 + 3 ^ 40 * 348626 * 2
def baseEnd_348626 : Nat := 179012706654458232871705

theorem tailTrace_348626 : CollatzResearch.WordTrace tailWord_348626 prefixEnd_348626 179012706654458232871705 := by
  unfold tailWord_348626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3178858708748754356410433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8476956556663344950427821 3178858708748754356410433)
  ·
    refine ⟨2384144031561565767307825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3178858708748754356410433 2384144031561565767307825)
    ·
      refine ⟨1788108023671174325480869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2384144031561565767307825 1788108023671174325480869)
      ·
        refine ⟨335270254438345186027663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1788108023671174325480869 335270254438345186027663)
        ·
          refine ⟨502905381657517779041495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335270254438345186027663 502905381657517779041495)
          ·
            refine ⟨754358072486276668562243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502905381657517779041495 754358072486276668562243)
            ·
              refine ⟨1131537108729415002843365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754358072486276668562243 1131537108729415002843365)
              ·
                refine ⟨212163207886765313033131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1131537108729415002843365 212163207886765313033131)
                ·
                  refine ⟨318244811830147969549697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212163207886765313033131 318244811830147969549697)
                  ·
                    refine ⟨238683608872610977162273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 318244811830147969549697 238683608872610977162273)
                    ·
                      refine ⟨179012706654458232871705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 238683608872610977162273 179012706654458232871705)
                      ·
                        rfl

theorem cell23_348626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_348626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348626 prefixEnd_348626 := by exact prefixLift 348626
  have htrace : WordTrace (prefixWord ++ tailWord_348626) baseStart_348626 baseEnd_348626 := by
    simpa [prefixWord, tailWord_348626, baseEnd_348626] using wordTrace_append hprefix tailTrace_348626
  have hstable : (prefixWord ++ tailWord_348626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348626).length < 2 ^ (prefixWord ++ tailWord_348626).sum := by decide
  have hdescent : baseEnd_348626 < baseStart_348626 := by decide
  rcases family_descends (prefixWord ++ tailWord_348626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348641 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 2, 6]
def baseStart_348641 : Nat := 118140960795 + 348641 * 2 ^ 59
def prefixEnd_348641 : Nat := 4983230072969 + 3 ^ 40 * 348641 * 2
def baseEnd_348641 : Nat := 59673469621425224728045

theorem tailTrace_348641 : CollatzResearch.WordTrace tailWord_348641 prefixEnd_348641 59673469621425224728045 := by
  unfold tailWord_348641
  simp only [CollatzResearch.WordTrace]
  refine ⟨12715981929940674987437777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8477321286627116658291851 12715981929940674987437777)
  ·
    refine ⟨9536986447455506240578333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12715981929940674987437777 9536986447455506240578333)
    ·
      refine ⟨3576369917795814840216875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9536986447455506240578333 3576369917795814840216875)
      ·
        refine ⟨5364554876693722260325313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3576369917795814840216875 5364554876693722260325313)
        ·
          refine ⟨4023416157520291695243985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5364554876693722260325313 4023416157520291695243985)
          ·
            refine ⟨3017562118140218771432989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4023416157520291695243985 3017562118140218771432989)
            ·
              refine ⟨1131585794302582039287371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3017562118140218771432989 1131585794302582039287371)
              ·
                refine ⟨1697378691453873058931057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131585794302582039287371 1697378691453873058931057)
                ·
                  refine ⟨1273034018590404794198293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1697378691453873058931057 1273034018590404794198293)
                  ·
                    refine ⟨59673469621425224728045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1273034018590404794198293 59673469621425224728045)
                    ·
                      rfl

theorem cell23_348641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_348641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348641 prefixEnd_348641 := by exact prefixLift 348641
  have htrace : WordTrace (prefixWord ++ tailWord_348641) baseStart_348641 baseEnd_348641 := by
    simpa [prefixWord, tailWord_348641, baseEnd_348641] using wordTrace_append hprefix tailTrace_348641
  have hstable : (prefixWord ++ tailWord_348641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348641).length < 2 ^ (prefixWord ++ tailWord_348641).sum := by decide
  have hdescent : baseEnd_348641 < baseStart_348641 := by decide
  rcases family_descends (prefixWord ++ tailWord_348641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348651 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 3]
def baseStart_348651 : Nat := 118140960795 + 348651 * 2 ^ 59
def prefixEnd_348651 : Nat := 4983230072969 + 3 ^ 40 * 348651 * 2
def baseEnd_348651 : Nat := 179025543670820635059089

theorem tailTrace_348651 : CollatzResearch.WordTrace tailWord_348651 prefixEnd_348651 179025543670820635059089 := by
  unfold tailWord_348651
  simp only [CollatzResearch.WordTrace]
  refine ⟨12716346659904446695301807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8477564439936297796867871 12716346659904446695301807)
  ·
    refine ⟨19074519989856670042952711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12716346659904446695301807 19074519989856670042952711)
    ·
      refine ⟨28611779984785005064429067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19074519989856670042952711 28611779984785005064429067)
      ·
        refine ⟨42917669977177507596643601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28611779984785005064429067 42917669977177507596643601)
        ·
          refine ⟨32188252482883130697482701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42917669977177507596643601 32188252482883130697482701)
          ·
            refine ⟨12070594681081174011556013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32188252482883130697482701 12070594681081174011556013)
            ·
              refine ⟨4526473005405440254333505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12070594681081174011556013 4526473005405440254333505)
              ·
                refine ⟨3394854754054080190750129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4526473005405440254333505 3394854754054080190750129)
                ·
                  refine ⟨2546141065540560143062597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3394854754054080190750129 2546141065540560143062597)
                  ·
                    refine ⟨477401449788855026824237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2546141065540560143062597 477401449788855026824237)
                    ·
                      refine ⟨179025543670820635059089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 477401449788855026824237 179025543670820635059089)
                      ·
                        rfl

theorem cell23_348651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 4, 3].length) (baseStart_348651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348651 prefixEnd_348651 := by exact prefixLift 348651
  have htrace : WordTrace (prefixWord ++ tailWord_348651) baseStart_348651 baseEnd_348651 := by
    simpa [prefixWord, tailWord_348651, baseEnd_348651] using wordTrace_append hprefix tailTrace_348651
  have hstable : (prefixWord ++ tailWord_348651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348651).length < 2 ^ (prefixWord ++ tailWord_348651).sum := by decide
  have hdescent : baseEnd_348651 < baseStart_348651 := by decide
  rcases family_descends (prefixWord ++ tailWord_348651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348698 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3]
def baseStart_348698 : Nat := 118140960795 + 348698 * 2 ^ 59
def prefixEnd_348698 : Nat := 4983230072969 + 3 ^ 40 * 348698 * 2
def baseEnd_348698 : Nat := 179049677261581951171373

theorem tailTrace_348698 : CollatzResearch.WordTrace tailWord_348698 prefixEnd_348698 179049677261581951171373 := by
  unfold tailWord_348698
  simp only [CollatzResearch.WordTrace]
  refine ⟨3179515222683543430565687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8478707260489449148175165 3179515222683543430565687)
  ·
    refine ⟨4769272834025315145848531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3179515222683543430565687 4769272834025315145848531)
    ·
      refine ⟨7153909251037972718772797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4769272834025315145848531 7153909251037972718772797)
      ·
        refine ⟨2682715969139239769539799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7153909251037972718772797 2682715969139239769539799)
        ·
          refine ⟨4024073953708859654309699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2682715969139239769539799 4024073953708859654309699)
          ·
            refine ⟨6036110930563289481464549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4024073953708859654309699 6036110930563289481464549)
            ·
              refine ⟨1131770799480616777774603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6036110930563289481464549 1131770799480616777774603)
              ·
                refine ⟨1697656199220925166661905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131770799480616777774603 1697656199220925166661905)
                ·
                  refine ⟨1273242149415693874996429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1697656199220925166661905 1273242149415693874996429)
                  ·
                    refine ⟨477465806030885203123661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1273242149415693874996429 477465806030885203123661)
                    ·
                      refine ⟨179049677261581951171373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 477465806030885203123661 179049677261581951171373)
                      ·
                        rfl

theorem cell23_348698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_348698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348698 prefixEnd_348698 := by exact prefixLift 348698
  have htrace : WordTrace (prefixWord ++ tailWord_348698) baseStart_348698 baseEnd_348698 := by
    simpa [prefixWord, tailWord_348698, baseEnd_348698] using wordTrace_append hprefix tailTrace_348698
  have hstable : (prefixWord ++ tailWord_348698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348698).length < 2 ^ (prefixWord ++ tailWord_348698).sum := by decide
  have hdescent : baseEnd_348698 < baseStart_348698 := by decide
  rcases family_descends (prefixWord ++ tailWord_348698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348751 : List Nat := [1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 6]
def baseStart_348751 : Nat := 118140960795 + 348751 * 2 ^ 59
def prefixEnd_348751 : Nat := 4983230072969 + 3 ^ 40 * 348751 * 2
def baseEnd_348751 : Nat := 179076891736270243808629

theorem tailTrace_348751 : CollatzResearch.WordTrace tailWord_348751 prefixEnd_348751 179076891736270243808629 := by
  unfold tailWord_348751
  simp only [CollatzResearch.WordTrace]
  refine ⟨12719993959542163773942107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8479995973028109182628071 12719993959542163773942107)
  ·
    refine ⟨19079990939313245660913161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12719993959542163773942107 19079990939313245660913161)
    ·
      refine ⟨14309993204484934245684871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19079990939313245660913161 14309993204484934245684871)
      ·
        refine ⟨21464989806727401368527307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14309993204484934245684871 21464989806727401368527307)
        ·
          refine ⟨32197484710091102052790961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21464989806727401368527307 32197484710091102052790961)
          ·
            refine ⟨24148113532568326539593221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32197484710091102052790961 24148113532568326539593221)
            ·
              refine ⟨4527771287356561226173729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24148113532568326539593221 4527771287356561226173729)
              ·
                refine ⟨3395828465517420919630297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4527771287356561226173729 3395828465517420919630297)
                ·
                  refine ⟨2546871349138065689722723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3395828465517420919630297 2546871349138065689722723)
                  ·
                    refine ⟨3820307023707098534584085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2546871349138065689722723 3820307023707098534584085)
                    ·
                      refine ⟨179076891736270243808629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 3820307023707098534584085 179076891736270243808629)
                      ·
                        rfl

theorem cell23_348751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_348751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348751 prefixEnd_348751 := by exact prefixLift 348751
  have htrace : WordTrace (prefixWord ++ tailWord_348751) baseStart_348751 baseEnd_348751 := by
    simpa [prefixWord, tailWord_348751, baseEnd_348751] using wordTrace_append hprefix tailTrace_348751
  have hstable : (prefixWord ++ tailWord_348751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348751).length < 2 ^ (prefixWord ++ tailWord_348751).sum := by decide
  have hdescent : baseEnd_348751 < baseStart_348751 := by decide
  rcases family_descends (prefixWord ++ tailWord_348751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348826 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3]
def baseStart_348826 : Nat := 118140960795 + 348826 * 2 ^ 59
def prefixEnd_348826 : Nat := 4983230072969 + 3 ^ 40 * 348826 * 2
def baseEnd_348826 : Nat := 179115402785357450370785

theorem tailTrace_348826 : CollatzResearch.WordTrace tailWord_348826 prefixEnd_348826 179115402785357450370785 := by
  unfold tailWord_348826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3180682358567612895730583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8481819622846967721948221 3180682358567612895730583)
  ·
    refine ⟨4771023537851419343595875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3180682358567612895730583 4771023537851419343595875)
    ·
      refine ⟨7156535306777129015393813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4771023537851419343595875 7156535306777129015393813)
      ·
        refine ⟨335462592505177922596585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7156535306777129015393813 335462592505177922596585)
        ·
          refine ⟨251596944378883441947439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335462592505177922596585 251596944378883441947439)
          ·
            refine ⟨377395416568325162921159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251596944378883441947439 377395416568325162921159)
            ·
              refine ⟨566093124852487744381739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377395416568325162921159 566093124852487744381739)
              ·
                refine ⟨849139687278731616572609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566093124852487744381739 849139687278731616572609)
                ·
                  refine ⟨636854765459048712429457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 849139687278731616572609 636854765459048712429457)
                  ·
                    refine ⟨477641074094286534322093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 636854765459048712429457 477641074094286534322093)
                    ·
                      refine ⟨179115402785357450370785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 477641074094286534322093 179115402785357450370785)
                      ·
                        rfl

theorem cell23_348826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_348826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348826 prefixEnd_348826 := by exact prefixLift 348826
  have htrace : WordTrace (prefixWord ++ tailWord_348826) baseStart_348826 baseEnd_348826 := by
    simpa [prefixWord, tailWord_348826, baseEnd_348826] using wordTrace_append hprefix tailTrace_348826
  have hstable : (prefixWord ++ tailWord_348826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348826).length < 2 ^ (prefixWord ++ tailWord_348826).sum := by decide
  have hdescent : baseEnd_348826 < baseStart_348826 := by decide
  rcases family_descends (prefixWord ++ tailWord_348826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348832 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 1, 5, 2]
def baseStart_348832 : Nat := 118140960795 + 348832 * 2 ^ 59
def prefixEnd_348832 : Nat := 4983230072969 + 3 ^ 40 * 348832 * 2
def baseEnd_348832 : Nat := 179118483669284426895757

theorem tailTrace_348832 : CollatzResearch.WordTrace tailWord_348832 prefixEnd_348832 179118483669284426895757 := by
  unfold tailWord_348832
  simp only [CollatzResearch.WordTrace]
  refine ⟨6361474136124357303820375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8481965514832476405093833 6361474136124357303820375)
  ·
    refine ⟨9542211204186535955730563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6361474136124357303820375 9542211204186535955730563)
    ·
      refine ⟨14313316806279803933595845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9542211204186535955730563 14313316806279803933595845)
      ·
        refine ⟨2683746901177463237549221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14313316806279803933595845 2683746901177463237549221)
        ·
          refine ⟨503202543970774357040479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2683746901177463237549221 503202543970774357040479)
          ·
            refine ⟨754803815956161535560719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503202543970774357040479 754803815956161535560719)
            ·
              refine ⟨1132205723934242303341079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754803815956161535560719 1132205723934242303341079)
              ·
                refine ⟨1698308585901363455011619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1132205723934242303341079 1698308585901363455011619)
                ·
                  refine ⟨2547462878852045182517429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1698308585901363455011619 2547462878852045182517429)
                  ·
                    refine ⟨238824644892379235861009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2547462878852045182517429 238824644892379235861009)
                    ·
                      refine ⟨179118483669284426895757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 238824644892379235861009 179118483669284426895757)
                      ·
                        rfl

theorem cell23_348832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_348832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_348832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_348832 prefixEnd_348832 := by exact prefixLift 348832
  have htrace : WordTrace (prefixWord ++ tailWord_348832) baseStart_348832 baseEnd_348832 := by
    simpa [prefixWord, tailWord_348832, baseEnd_348832] using wordTrace_append hprefix tailTrace_348832
  have hstable : (prefixWord ++ tailWord_348832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348832).length < 2 ^ (prefixWord ++ tailWord_348832).sum := by decide
  have hdescent : baseEnd_348832 < baseStart_348832 := by decide
  rcases family_descends (prefixWord ++ tailWord_348832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
