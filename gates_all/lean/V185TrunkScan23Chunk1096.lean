import V185TrunkScan23Chunk1095

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6488949 : List Nat := [1, 3, 4, 1, 1, 2, 1, 4, 1, 3, 2]
def baseStart_6488949 : Nat := 118140960795 + 6488949 * 2 ^ 59
def prefixEnd_6488949 : Nat := 4983230072969 + 3 ^ 40 * 6488949 * 2
def baseEnd_6488949 : Nat := 3331949779511837690895373

theorem tailTrace_6488949 : CollatzResearch.WordTrace tailWord_6488949 prefixEnd_6488949 3331949779511837690895373 := by
  unfold tailWord_6488949
  simp only [CollatzResearch.WordTrace]
  refine ⟨236671413368653472104069901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157780942245768981402713267 236671413368653472104069901)
  ·
    refine ⟨88751780013245052039026213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236671413368653472104069901 88751780013245052039026213)
    ·
      refine ⟨16640958752483447257317415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88751780013245052039026213 16640958752483447257317415)
      ·
        refine ⟨24961438128725170885976123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16640958752483447257317415 24961438128725170885976123)
        ·
          refine ⟨37442157193087756328964185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24961438128725170885976123 37442157193087756328964185)
          ·
            refine ⟨28081617894815817246723139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37442157193087756328964185 28081617894815817246723139)
            ·
              refine ⟨42122426842223725870084709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28081617894815817246723139 42122426842223725870084709)
              ·
                refine ⟨7897955032916948600640883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42122426842223725870084709 7897955032916948600640883)
                ·
                  refine ⟨11846932549375422900961325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7897955032916948600640883 11846932549375422900961325)
                  ·
                    refine ⟨4442599706015783587860497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11846932549375422900961325 4442599706015783587860497)
                    ·
                      refine ⟨3331949779511837690895373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4442599706015783587860497 3331949779511837690895373)
                      ·
                        rfl

theorem cell23_6488949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_6488949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488949 prefixEnd_6488949 := by exact prefixLift 6488949
  have htrace : WordTrace (prefixWord ++ tailWord_6488949) baseStart_6488949 baseEnd_6488949 := by
    simpa [prefixWord, tailWord_6488949, baseEnd_6488949] using wordTrace_append hprefix tailTrace_6488949
  have hstable : (prefixWord ++ tailWord_6488949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488949).length < 2 ^ (prefixWord ++ tailWord_6488949).sum := by decide
  have hdescent : baseEnd_6488949 < baseStart_6488949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488965 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 2, 1, 5]
def baseStart_6488965 : Nat := 118140960795 + 6488965 * 2 ^ 59
def prefixEnd_6488965 : Nat := 4983230072969 + 3 ^ 40 * 6488965 * 2
def baseEnd_6488965 : Nat := 3331957995202309628295299

theorem tailTrace_6488965 : CollatzResearch.WordTrace tailWord_6488965 prefixEnd_6488965 3331957995202309628295299 := by
  unfold tailWord_6488965
  simp only [CollatzResearch.WordTrace]
  refine ⟨236671996936595506836652349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157781331291063671224434899 236671996936595506836652349)
  ·
    refine ⟨88751998851223315063744631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236671996936595506836652349 88751998851223315063744631)
    ·
      refine ⟨133127998276834972595616947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88751998851223315063744631 133127998276834972595616947)
      ·
        refine ⟨199691997415252458893425421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133127998276834972595616947 199691997415252458893425421)
        ·
          refine ⟨74884499030719672085034533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199691997415252458893425421 74884499030719672085034533)
          ·
            refine ⟨14040843568259938515943975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74884499030719672085034533 14040843568259938515943975)
            ·
              refine ⟨21061265352389907773915963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14040843568259938515943975 21061265352389907773915963)
              ·
                refine ⟨31591898028584861660873945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21061265352389907773915963 31591898028584861660873945)
                ·
                  refine ⟨23693923521438646245655459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31591898028584861660873945 23693923521438646245655459)
                  ·
                    refine ⟨35540885282157969368483189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23693923521438646245655459 35540885282157969368483189)
                    ·
                      refine ⟨3331957995202309628295299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35540885282157969368483189 3331957995202309628295299)
                      ·
                        rfl

theorem cell23_6488965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_6488965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488965 prefixEnd_6488965 := by exact prefixLift 6488965
  have htrace : WordTrace (prefixWord ++ tailWord_6488965) baseStart_6488965 baseEnd_6488965 := by
    simpa [prefixWord, tailWord_6488965, baseEnd_6488965] using wordTrace_append hprefix tailTrace_6488965
  have hstable : (prefixWord ++ tailWord_6488965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488965).length < 2 ^ (prefixWord ++ tailWord_6488965).sum := by decide
  have hdescent : baseEnd_6488965 < baseStart_6488965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6488995 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 3]
def baseStart_6488995 : Nat := 118140960795 + 6488995 * 2 ^ 59
def prefixEnd_6488995 : Nat := 4983230072969 + 3 ^ 40 * 6488995 * 2
def baseEnd_6488995 : Nat := 3331973399621944510920161

theorem tailTrace_6488995 : CollatzResearch.WordTrace tailWord_6488995 prefixEnd_6488995 3331973399621944510920161 := by
  unfold tailWord_6488995
  simp only [CollatzResearch.WordTrace]
  refine ⟨236673091126486821960244439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157782060750991214640162959 236673091126486821960244439)
  ·
    refine ⟨355009636689730232940366659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236673091126486821960244439 355009636689730232940366659)
    ·
      refine ⟨532514455034595349410549989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355009636689730232940366659 532514455034595349410549989)
      ·
        refine ⟨99846460318986628014478123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 532514455034595349410549989 99846460318986628014478123)
        ·
          refine ⟨149769690478479942021717185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99846460318986628014478123 149769690478479942021717185)
          ·
            refine ⟨112327267858859956516287889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149769690478479942021717185 112327267858859956516287889)
            ·
              refine ⟨84245450894144967387215917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112327267858859956516287889 84245450894144967387215917)
              ·
                refine ⟨31592044085304362770205969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84245450894144967387215917 31592044085304362770205969)
                ·
                  refine ⟨23694033063978272077654477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31592044085304362770205969 23694033063978272077654477)
                  ·
                    refine ⟨8885262398991852029120429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23694033063978272077654477 8885262398991852029120429)
                    ·
                      refine ⟨3331973399621944510920161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8885262398991852029120429 3331973399621944510920161)
                      ·
                        rfl

theorem cell23_6488995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_6488995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6488995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6488995 prefixEnd_6488995 := by exact prefixLift 6488995
  have htrace : WordTrace (prefixWord ++ tailWord_6488995) baseStart_6488995 baseEnd_6488995 := by
    simpa [prefixWord, tailWord_6488995, baseEnd_6488995] using wordTrace_append hprefix tailTrace_6488995
  have hstable : (prefixWord ++ tailWord_6488995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6488995).length < 2 ^ (prefixWord ++ tailWord_6488995).sum := by decide
  have hdescent : baseEnd_6488995 < baseStart_6488995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6488995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489015 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 2, 5]
def baseStart_6489015 : Nat := 118140960795 + 6489015 * 2 ^ 59
def prefixEnd_6489015 : Nat := 4983230072969 + 3 ^ 40 * 6489015 * 2
def baseEnd_6489015 : Nat := 1110661223078344810890023

theorem tailTrace_6489015 : CollatzResearch.WordTrace tailWord_6489015 prefixEnd_6489015 1110661223078344810890023 := by
  unfold tailWord_6489015
  simp only [CollatzResearch.WordTrace]
  refine ⟨236673820586414365375972499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157782547057609576917314999 236673820586414365375972499)
  ·
    refine ⟨355010730879621548063958749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236673820586414365375972499 355010730879621548063958749)
    ·
      refine ⟨133129024079858080523984531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355010730879621548063958749 133129024079858080523984531)
      ·
        refine ⟨199693536119787120785976797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133129024079858080523984531 199693536119787120785976797)
        ·
          refine ⟨74885076044920170294741299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199693536119787120785976797 74885076044920170294741299)
          ·
            refine ⟨112327614067380255442111949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74885076044920170294741299 112327614067380255442111949)
            ·
              refine ⟨42122855275267595790791981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112327614067380255442111949 42122855275267595790791981)
              ·
                refine ⟨15796070728225348421546993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42122855275267595790791981 15796070728225348421546993)
                ·
                  refine ⟨11847053046169011316160245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15796070728225348421546993 11847053046169011316160245)
                  ·
                    refine ⟨1110661223078344810890023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11847053046169011316160245 1110661223078344810890023)
                    ·
                      rfl

theorem cell23_6489015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_6489015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489015 prefixEnd_6489015 := by exact prefixLift 6489015
  have htrace : WordTrace (prefixWord ++ tailWord_6489015) baseStart_6489015 baseEnd_6489015 := by
    simpa [prefixWord, tailWord_6489015, baseEnd_6489015] using wordTrace_append hprefix tailTrace_6489015
  have hstable : (prefixWord ++ tailWord_6489015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489015).length < 2 ^ (prefixWord ++ tailWord_6489015).sum := by decide
  have hdescent : baseEnd_6489015 < baseStart_6489015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489042 : List Nat := [3, 2, 2, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_6489042 : Nat := 118140960795 + 6489042 * 2 ^ 59
def prefixEnd_6489042 : Nat := 4983230072969 + 3 ^ 40 * 6489042 * 2
def baseEnd_6489042 : Nat := 3331997533212705827032445

theorem tailTrace_6489042 : CollatzResearch.WordTrace tailWord_6489042 prefixEnd_6489042 3331997533212705827032445 := by
  unfold tailWord_6489042
  simp only [CollatzResearch.WordTrace]
  refine ⟨59168701339329137246801345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157783203571544365991470253 59168701339329137246801345)
  ·
    refine ⟨44376526004496852935101009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59168701339329137246801345 44376526004496852935101009)
    ·
      refine ⟨33282394503372639701325757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44376526004496852935101009 33282394503372639701325757)
      ·
        refine ⟨12480897938764739887997159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33282394503372639701325757 12480897938764739887997159)
        ·
          refine ⟨18721346908147109831995739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12480897938764739887997159 18721346908147109831995739)
          ·
            refine ⟨28082020362220664747993609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18721346908147109831995739 28082020362220664747993609)
            ·
              refine ⟨21061515271665498560995207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28082020362220664747993609 21061515271665498560995207)
              ·
                refine ⟨31592272907498247841492811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21061515271665498560995207 31592272907498247841492811)
                ·
                  refine ⟨47388409361247371762239217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31592272907498247841492811 47388409361247371762239217)
                  ·
                    refine ⟨35541307020935528821679413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47388409361247371762239217 35541307020935528821679413)
                    ·
                      refine ⟨3331997533212705827032445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35541307020935528821679413 3331997533212705827032445)
                      ·
                        rfl

theorem cell23_6489042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_6489042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489042 prefixEnd_6489042 := by exact prefixLift 6489042
  have htrace : WordTrace (prefixWord ++ tailWord_6489042) baseStart_6489042 baseEnd_6489042 := by
    simpa [prefixWord, tailWord_6489042, baseEnd_6489042] using wordTrace_append hprefix tailTrace_6489042
  have hstable : (prefixWord ++ tailWord_6489042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489042).length < 2 ^ (prefixWord ++ tailWord_6489042).sum := by decide
  have hdescent : baseEnd_6489042 < baseStart_6489042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489095 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_6489095 : Nat := 118140960795 + 6489095 * 2 ^ 59
def prefixEnd_6489095 : Nat := 4983230072969 + 3 ^ 40 * 6489095 * 2
def baseEnd_6489095 : Nat := 3332024747687394119669701

theorem tailTrace_6489095 : CollatzResearch.WordTrace tailWord_6489095 prefixEnd_6489095 3332024747687394119669701 := by
  unfold tailWord_6489095
  simp only [CollatzResearch.WordTrace]
  refine ⟨236676738426124539038884739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157784492284083026025923159 236676738426124539038884739)
  ·
    refine ⟨355015107639186808558327109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236676738426124539038884739 355015107639186808558327109)
    ·
      refine ⟨66565332682347526604686333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 355015107639186808558327109 66565332682347526604686333)
      ·
        refine ⟨24961999755880322476757375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66565332682347526604686333 24961999755880322476757375)
        ·
          refine ⟨37442999633820483715136063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24961999755880322476757375 37442999633820483715136063)
          ·
            refine ⟨56164499450730725572704095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37442999633820483715136063 56164499450730725572704095)
            ·
              refine ⟨84246749176096088359056143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56164499450730725572704095 84246749176096088359056143)
              ·
                refine ⟨126370123764144132538584215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84246749176096088359056143 126370123764144132538584215)
                ·
                  refine ⟨189555185646216198807876323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126370123764144132538584215 189555185646216198807876323)
                  ·
                    refine ⟨284332778469324298211814485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 189555185646216198807876323 284332778469324298211814485)
                    ·
                      refine ⟨3332024747687394119669701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 284332778469324298211814485 3332024747687394119669701)
                      ·
                        rfl

theorem cell23_6489095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_6489095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489095 prefixEnd_6489095 := by exact prefixLift 6489095
  have htrace : WordTrace (prefixWord ++ tailWord_6489095) baseStart_6489095 baseEnd_6489095 := by
    simpa [prefixWord, tailWord_6489095, baseEnd_6489095] using wordTrace_append hprefix tailTrace_6489095
  have hstable : (prefixWord ++ tailWord_6489095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489095).length < 2 ^ (prefixWord ++ tailWord_6489095).sum := by decide
  have hdescent : baseEnd_6489095 < baseStart_6489095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489105 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 5, 5]
def baseStart_6489105 : Nat := 118140960795 + 6489105 * 2 ^ 59
def prefixEnd_6489105 : Nat := 4983230072969 + 3 ^ 40 * 6489105 * 2
def baseEnd_6489105 : Nat := 1110676627497979693514885

theorem tailTrace_6489105 : CollatzResearch.WordTrace tailWord_6489105 prefixEnd_6489105 1110676627497979693514885 := by
  unfold tailWord_6489105
  simp only [CollatzResearch.WordTrace]
  refine ⟨236677103156088310746748769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157784735437392207164499179 236677103156088310746748769)
  ·
    refine ⟨177507827367066233060061577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236677103156088310746748769 177507827367066233060061577)
    ·
      refine ⟨133130870525299674795046183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177507827367066233060061577 133130870525299674795046183)
      ·
        refine ⟨199696305787949512192569275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133130870525299674795046183 199696305787949512192569275)
        ·
          refine ⟨299544458681924268288853913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199696305787949512192569275 299544458681924268288853913)
          ·
            refine ⟨224658344011443201216640435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299544458681924268288853913 224658344011443201216640435)
            ·
              refine ⟨336987516017164801824960653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224658344011443201216640435 336987516017164801824960653)
              ·
                refine ⟨126370318506436800684360245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 336987516017164801824960653 126370318506436800684360245)
                ·
                  refine ⟨11847217359978450064158773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126370318506436800684360245 11847217359978450064158773)
                  ·
                    refine ⟨1110676627497979693514885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11847217359978450064158773 1110676627497979693514885)
                    ·
                      rfl

theorem cell23_6489105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_6489105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489105 prefixEnd_6489105 := by exact prefixLift 6489105
  have htrace : WordTrace (prefixWord ++ tailWord_6489105) baseStart_6489105 baseEnd_6489105 := by
    simpa [prefixWord, tailWord_6489105, baseEnd_6489105] using wordTrace_append hprefix tailTrace_6489105
  have hstable : (prefixWord ++ tailWord_6489105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489105).length < 2 ^ (prefixWord ++ tailWord_6489105).sum := by decide
  have hdescent : baseEnd_6489105 < baseStart_6489105 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489109 : List Nat := [1, 3, 2, 1, 4, 2, 3, 1, 6]
def baseStart_6489109 : Nat := 118140960795 + 6489109 * 2 ^ 59
def prefixEnd_6489109 : Nat := 4983230072969 + 3 ^ 40 * 6489109 * 2
def baseEnd_6489109 : Nat := 370225770712950784988293

theorem tailTrace_6489109 : CollatzResearch.WordTrace tailWord_6489109 prefixEnd_6489109 370225770712950784988293 := by
  unfold tailWord_6489109
  simp only [CollatzResearch.WordTrace]
  refine ⟨236677249048073819429894381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157784832698715879619929587 236677249048073819429894381)
  ·
    refine ⟨88753968393027682286210393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236677249048073819429894381 88753968393027682286210393)
    ·
      refine ⟨66565476294770761714657795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88753968393027682286210393 66565476294770761714657795)
      ·
        refine ⟨99848214442156142571986693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66565476294770761714657795 99848214442156142571986693)
        ·
          refine ⟨18721540207904276732247505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99848214442156142571986693 18721540207904276732247505)
          ·
            refine ⟨14041155155928207549185629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18721540207904276732247505 14041155155928207549185629)
            ·
              refine ⟨5265433183473077830944611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14041155155928207549185629 5265433183473077830944611)
              ·
                refine ⟨7898149775209616746416917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5265433183473077830944611 7898149775209616746416917)
                ·
                  refine ⟨370225770712950784988293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7898149775209616746416917 370225770712950784988293)
                  ·
                    rfl

theorem cell23_6489109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 6].length) (baseStart_6489109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489109 prefixEnd_6489109 := by exact prefixLift 6489109
  have htrace : WordTrace (prefixWord ++ tailWord_6489109) baseStart_6489109 baseEnd_6489109 := by
    simpa [prefixWord, tailWord_6489109, baseEnd_6489109] using wordTrace_append hprefix tailTrace_6489109
  have hstable : (prefixWord ++ tailWord_6489109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489109).length < 2 ^ (prefixWord ++ tailWord_6489109).sum := by decide
  have hdescent : baseEnd_6489109 < baseStart_6489109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489119 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 3, 1, 3]
def baseStart_6489119 : Nat := 118140960795 + 6489119 * 2 ^ 59
def prefixEnd_6489119 : Nat := 4983230072969 + 3 ^ 40 * 6489119 * 2
def baseEnd_6489119 : Nat := 3332037071223102025769591

theorem tailTrace_6489119 : CollatzResearch.WordTrace tailWord_6489119 prefixEnd_6489119 3332037071223102025769591 := by
  unfold tailWord_6489119
  simp only [CollatzResearch.WordTrace]
  refine ⟨236677613778037591137758411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157785075852025060758505607 236677613778037591137758411)
  ·
    refine ⟨355016420667056386706637617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236677613778037591137758411 355016420667056386706637617)
    ·
      refine ⟨266262315500292290029978213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355016420667056386706637617 266262315500292290029978213)
      ·
        refine ⟨49924184156304804380620915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 266262315500292290029978213 49924184156304804380620915)
        ·
          refine ⟨74886276234457206570931373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49924184156304804380620915 74886276234457206570931373)
          ·
            refine ⟨28082353587921452464099265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74886276234457206570931373 28082353587921452464099265)
            ·
              refine ⟨21061765190941089348074449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28082353587921452464099265 21061765190941089348074449)
              ·
                refine ⟨15796323893205817011055837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21061765190941089348074449 15796323893205817011055837)
                ·
                  refine ⟨5923621459952181379145939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15796323893205817011055837 5923621459952181379145939)
                  ·
                    refine ⟨8885432189928272068718909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5923621459952181379145939 8885432189928272068718909)
                    ·
                      refine ⟨3332037071223102025769591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8885432189928272068718909 3332037071223102025769591)
                      ·
                        rfl

theorem cell23_6489119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_6489119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489119 prefixEnd_6489119 := by exact prefixLift 6489119
  have htrace : WordTrace (prefixWord ++ tailWord_6489119) baseStart_6489119 baseEnd_6489119 := by
    simpa [prefixWord, tailWord_6489119, baseEnd_6489119] using wordTrace_append hprefix tailTrace_6489119
  have hstable : (prefixWord ++ tailWord_6489119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489119).length < 2 ^ (prefixWord ++ tailWord_6489119).sum := by decide
  have hdescent : baseEnd_6489119 < baseStart_6489119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489130 : List Nat := [3, 1, 4, 1, 4, 1, 1, 3, 1, 4]
def baseStart_6489130 : Nat := 118140960795 + 6489130 * 2 ^ 59
def prefixEnd_6489130 : Nat := 4983230072969 + 3 ^ 40 * 6489130 * 2
def baseEnd_6489130 : Nat := 1110680906503433827577347

theorem tailTrace_6489130 : CollatzResearch.WordTrace tailWord_6489130 prefixEnd_6489130 1110680906503433827577347 := by
  unfold tailWord_6489130
  simp only [CollatzResearch.WordTrace]
  refine ⟨59169503745249435004102211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157785343320665160010939229 59169503745249435004102211)
  ·
    refine ⟨88754255617874152506153317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59169503745249435004102211 88754255617874152506153317)
    ·
      refine ⟨16641422928351403594903747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88754255617874152506153317 16641422928351403594903747)
      ·
        refine ⟨24962134392527105392355621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16641422928351403594903747 24962134392527105392355621)
        ·
          refine ⟨4680400198598832261066679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24962134392527105392355621 4680400198598832261066679)
          ·
            refine ⟨7020600297898248391600019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680400198598832261066679 7020600297898248391600019)
            ·
              refine ⟨10530900446847372587400029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7020600297898248391600019 10530900446847372587400029)
              ·
                refine ⟨3949087667567764720275011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10530900446847372587400029 3949087667567764720275011)
                ·
                  refine ⟨5923631501351647080412517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3949087667567764720275011 5923631501351647080412517)
                  ·
                    refine ⟨1110680906503433827577347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5923631501351647080412517 1110680906503433827577347)
                    ·
                      rfl

theorem cell23_6489130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_6489130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489130 prefixEnd_6489130 := by exact prefixLift 6489130
  have htrace : WordTrace (prefixWord ++ tailWord_6489130) baseStart_6489130 baseEnd_6489130 := by
    simpa [prefixWord, tailWord_6489130, baseEnd_6489130] using wordTrace_append hprefix tailTrace_6489130
  have hstable : (prefixWord ++ tailWord_6489130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489130).length < 2 ^ (prefixWord ++ tailWord_6489130).sum := by decide
  have hdescent : baseEnd_6489130 < baseStart_6489130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489152 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 4, 4]
def baseStart_6489152 : Nat := 118140960795 + 6489152 * 2 ^ 59
def prefixEnd_6489152 : Nat := 4983230072969 + 3 ^ 40 * 6489152 * 2
def baseEnd_6489152 : Nat := 1110684672028233465552313

theorem tailTrace_6489152 : CollatzResearch.WordTrace tailWord_6489152 prefixEnd_6489152 1110684672028233465552313 := by
  unfold tailWord_6489152
  simp only [CollatzResearch.WordTrace]
  refine ⟨118339408693459018886854855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157785878257945358515806473 118339408693459018886854855)
  ·
    refine ⟨177509113040188528330282283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118339408693459018886854855 177509113040188528330282283)
    ·
      refine ⟨266263669560282792495423425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177509113040188528330282283 266263669560282792495423425)
      ·
        refine ⟨199697752170212094371567569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266263669560282792495423425 199697752170212094371567569)
        ·
          refine ⟨149773314127659070778675677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199697752170212094371567569 149773314127659070778675677)
          ·
            refine ⟨56164992797872151542003379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149773314127659070778675677 56164992797872151542003379)
            ·
              refine ⟨84247489196808227313005069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56164992797872151542003379 84247489196808227313005069)
              ·
                refine ⟨31592808448803085242376901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84247489196808227313005069 31592808448803085242376901)
                ·
                  refine ⟨5923651584150578482945669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31592808448803085242376901 5923651584150578482945669)
                  ·
                    refine ⟨1110684672028233465552313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5923651584150578482945669 1110684672028233465552313)
                    ·
                      rfl

theorem cell23_6489152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 4, 4].length) (baseStart_6489152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489152 prefixEnd_6489152 := by exact prefixLift 6489152
  have htrace : WordTrace (prefixWord ++ tailWord_6489152) baseStart_6489152 baseEnd_6489152 := by
    simpa [prefixWord, tailWord_6489152, baseEnd_6489152] using wordTrace_append hprefix tailTrace_6489152
  have hstable : (prefixWord ++ tailWord_6489152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489152).length < 2 ^ (prefixWord ++ tailWord_6489152).sum := by decide
  have hdescent : baseEnd_6489152 < baseStart_6489152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489153 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_6489153 : Nat := 118140960795 + 6489153 * 2 ^ 59
def prefixEnd_6489153 : Nat := 4983230072969 + 3 ^ 40 * 6489153 * 2
def baseEnd_6489153 : Nat := 3332054529565354892744435

theorem tailTrace_6489153 : CollatzResearch.WordTrace tailWord_6489153 prefixEnd_6489153 3332054529565354892744435 := by
  unfold tailWord_6489153
  simp only [CollatzResearch.WordTrace]
  refine ⟨236678853859914414944496113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157785902573276276629664075 236678853859914414944496113)
  ·
    refine ⟨177509140394935811208372085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236678853859914414944496113 177509140394935811208372085)
    ·
      refine ⟨16641481912025232300784883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177509140394935811208372085 16641481912025232300784883)
      ·
        refine ⟨24962222868037848451177325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16641481912025232300784883 24962222868037848451177325)
        ·
          refine ⟨9360833575514193169191497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24962222868037848451177325 9360833575514193169191497)
          ·
            refine ⟨7020625181635644876893623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9360833575514193169191497 7020625181635644876893623)
            ·
              refine ⟨10530937772453467315340435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7020625181635644876893623 10530937772453467315340435)
              ·
                refine ⟨15796406658680200973010653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10530937772453467315340435 15796406658680200973010653)
                ·
                  refine ⟨5923652497005075364878995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15796406658680200973010653 5923652497005075364878995)
                  ·
                    refine ⟨8885478745507613047318493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5923652497005075364878995 8885478745507613047318493)
                    ·
                      refine ⟨3332054529565354892744435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8885478745507613047318493 3332054529565354892744435)
                      ·
                        rfl

theorem cell23_6489153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_6489153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489153 prefixEnd_6489153 := by exact prefixLift 6489153
  have htrace : WordTrace (prefixWord ++ tailWord_6489153) baseStart_6489153 baseEnd_6489153 := by
    simpa [prefixWord, tailWord_6489153, baseEnd_6489153] using wordTrace_append hprefix tailTrace_6489153
  have hstable : (prefixWord ++ tailWord_6489153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489153).length < 2 ^ (prefixWord ++ tailWord_6489153).sum := by decide
  have hdescent : baseEnd_6489153 < baseStart_6489153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489155 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 6]
def baseStart_6489155 : Nat := 118140960795 + 6489155 * 2 ^ 59
def prefixEnd_6489155 : Nat := 4983230072969 + 3 ^ 40 * 6489155 * 2
def baseEnd_6489155 : Nat := 3332055556526663884919425

theorem tailTrace_6489155 : CollatzResearch.WordTrace tailWord_6489155 prefixEnd_6489155 3332055556526663884919425 := by
  unfold tailWord_6489155
  simp only [CollatzResearch.WordTrace]
  refine ⟨236678926805907169286068919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157785951203938112857379279 236678926805907169286068919)
  ·
    refine ⟨355018390208860753929103379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236678926805907169286068919 355018390208860753929103379)
    ·
      refine ⟨532527585313291130893655069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355018390208860753929103379 532527585313291130893655069)
      ·
        refine ⟨199697844492484174085120651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 532527585313291130893655069 199697844492484174085120651)
        ·
          refine ⟨299546766738726261127680977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199697844492484174085120651 299546766738726261127680977)
          ·
            refine ⟨224660075054044695845760733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299546766738726261127680977 224660075054044695845760733)
            ·
              refine ⟨84247528145266760942160275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224660075054044695845760733 84247528145266760942160275)
              ·
                refine ⟨126371292217900141413240413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84247528145266760942160275 126371292217900141413240413)
                ·
                  refine ⟨47389234581712553029965155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126371292217900141413240413 47389234581712553029965155)
                  ·
                    refine ⟨71083851872568829544947733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47389234581712553029965155 71083851872568829544947733)
                    ·
                      refine ⟨3332055556526663884919425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71083851872568829544947733 3332055556526663884919425)
                      ·
                        rfl

theorem cell23_6489155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_6489155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489155 prefixEnd_6489155 := by exact prefixLift 6489155
  have htrace : WordTrace (prefixWord ++ tailWord_6489155) baseStart_6489155 baseEnd_6489155 := by
    simpa [prefixWord, tailWord_6489155, baseEnd_6489155] using wordTrace_append hprefix tailTrace_6489155
  have hstable : (prefixWord ++ tailWord_6489155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489155).length < 2 ^ (prefixWord ++ tailWord_6489155).sum := by decide
  have hdescent : baseEnd_6489155 < baseStart_6489155 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489162 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_6489162 : Nat := 118140960795 + 6489162 * 2 ^ 59
def prefixEnd_6489162 : Nat := 4983230072969 + 3 ^ 40 * 6489162 * 2
def baseEnd_6489162 : Nat := 3332059150891245357531893

theorem tailTrace_6489162 : CollatzResearch.WordTrace tailWord_6489162 prefixEnd_6489162 3332059150891245357531893 := by
  unfold tailWord_6489162
  simp only [CollatzResearch.WordTrace]
  refine ⟨59169795529220452370393435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157786121411254539654382493 59169795529220452370393435)
  ·
    refine ⟨88754693293830678555590153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59169795529220452370393435 88754693293830678555590153)
    ·
      refine ⟨66566019970373008916692615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88754693293830678555590153 66566019970373008916692615)
      ·
        refine ⟨99849029955559513375038923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66566019970373008916692615 99849029955559513375038923)
        ·
          refine ⟨149773544933339270062558385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99849029955559513375038923 149773544933339270062558385)
          ·
            refine ⟨112330158700004452546918789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149773544933339270062558385 112330158700004452546918789)
            ·
              refine ⟨21061904756250834852547273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112330158700004452546918789 21061904756250834852547273)
              ·
                refine ⟨15796428567188126139410455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21061904756250834852547273 15796428567188126139410455)
                ·
                  refine ⟨23694642850782189209115683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15796428567188126139410455 23694642850782189209115683)
                  ·
                    refine ⟨35541964276173283813673525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23694642850782189209115683 35541964276173283813673525)
                    ·
                      refine ⟨3332059150891245357531893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35541964276173283813673525 3332059150891245357531893)
                      ·
                        rfl

theorem cell23_6489162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_6489162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489162 prefixEnd_6489162 := by exact prefixLift 6489162
  have htrace : WordTrace (prefixWord ++ tailWord_6489162) baseStart_6489162 baseEnd_6489162 := by
    simpa [prefixWord, tailWord_6489162, baseEnd_6489162] using wordTrace_append hprefix tailTrace_6489162
  have hstable : (prefixWord ++ tailWord_6489162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489162).length < 2 ^ (prefixWord ++ tailWord_6489162).sum := by decide
  have hdescent : baseEnd_6489162 < baseStart_6489162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489172 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_6489172 : Nat := 118140960795 + 6489172 * 2 ^ 59
def prefixEnd_6489172 : Nat := 4983230072969 + 3 ^ 40 * 6489172 * 2
def baseEnd_6489172 : Nat := 3332064285697790318406847

theorem tailTrace_6489172 : CollatzResearch.WordTrace tailWord_6489172 prefixEnd_6489172 3332064285697790318406847 := by
  unfold tailWord_6489172
  simp only [CollatzResearch.WordTrace]
  refine ⟨118339773423422790594718885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157786364564563720792958513 118339773423422790594718885)
  ·
    refine ⟨22188707516891773236509791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118339773423422790594718885 22188707516891773236509791)
    ·
      refine ⟨33283061275337659854764687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22188707516891773236509791 33283061275337659854764687)
      ·
        refine ⟨49924591913006489782147031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33283061275337659854764687 49924591913006489782147031)
        ·
          refine ⟨74886887869509734673220547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49924591913006489782147031 74886887869509734673220547)
          ·
            refine ⟨112330331804264602009830821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74886887869509734673220547 112330331804264602009830821)
            ·
              refine ⟨21061937213299612876843279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112330331804264602009830821 21061937213299612876843279)
              ·
                refine ⟨31592905819949419315264919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21061937213299612876843279 31592905819949419315264919)
                ·
                  refine ⟨47389358729924128972897379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31592905819949419315264919 47389358729924128972897379)
                  ·
                    refine ⟨71084038094886193459346069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47389358729924128972897379 71084038094886193459346069)
                    ·
                      refine ⟨3332064285697790318406847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71084038094886193459346069 3332064285697790318406847)
                      ·
                        rfl

theorem cell23_6489172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_6489172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489172 prefixEnd_6489172 := by exact prefixLift 6489172
  have htrace : WordTrace (prefixWord ++ tailWord_6489172) baseStart_6489172 baseEnd_6489172 := by
    simpa [prefixWord, tailWord_6489172, baseEnd_6489172] using wordTrace_append hprefix tailTrace_6489172
  have hstable : (prefixWord ++ tailWord_6489172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489172).length < 2 ^ (prefixWord ++ tailWord_6489172).sum := by decide
  have hdescent : baseEnd_6489172 < baseStart_6489172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489195 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 6, 7]
def baseStart_6489195 : Nat := 118140960795 + 6489195 * 2 ^ 59
def prefixEnd_6489195 : Nat := 4983230072969 + 3 ^ 40 * 6489195 * 2
def baseEnd_6489195 : Nat := 1110692031917614576139747

theorem tailTrace_6489195 : CollatzResearch.WordTrace tailWord_6489195 prefixEnd_6489195 1110692031917614576139747 := by
  unfold tailWord_6489195
  simp only [CollatzResearch.WordTrace]
  refine ⟨236680385725762256117525039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157786923817174837411683359 236680385725762256117525039)
  ·
    refine ⟨355020578588643384176287559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236680385725762256117525039 355020578588643384176287559)
    ·
      refine ⟨532530867882965076264431339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355020578588643384176287559 532530867882965076264431339)
      ·
        refine ⟨798796301824447614396647009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532530867882965076264431339 798796301824447614396647009)
        ·
          refine ⟨599097226368335710797485257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 798796301824447614396647009 599097226368335710797485257)
          ·
            refine ⟨449322919776251783098113943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599097226368335710797485257 449322919776251783098113943)
            ·
              refine ⟨673984379664377674647170915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449322919776251783098113943 673984379664377674647170915)
              ·
                refine ⟨1010976569496566511970756373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673984379664377674647170915 1010976569496566511970756373)
                ·
                  refine ⟨47389526695151555248629205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1010976569496566511970756373 47389526695151555248629205)
                  ·
                    refine ⟨1110692031917614576139747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47389526695151555248629205 1110692031917614576139747)
                    ·
                      rfl

theorem cell23_6489195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 7].length) (baseStart_6489195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489195 prefixEnd_6489195 := by exact prefixLift 6489195
  have htrace : WordTrace (prefixWord ++ tailWord_6489195) baseStart_6489195 baseEnd_6489195 := by
    simpa [prefixWord, tailWord_6489195, baseEnd_6489195] using wordTrace_append hprefix tailTrace_6489195
  have hstable : (prefixWord ++ tailWord_6489195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489195).length < 2 ^ (prefixWord ++ tailWord_6489195).sum := by decide
  have hdescent : baseEnd_6489195 < baseStart_6489195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489196 : List Nat := [2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 3]
def baseStart_6489196 : Nat := 118140960795 + 6489196 * 2 ^ 59
def prefixEnd_6489196 : Nat := 4983230072969 + 3 ^ 40 * 6489196 * 2
def baseEnd_6489196 : Nat := 3332076609233498224506737

theorem tailTrace_6489196 : CollatzResearch.WordTrace tailWord_6489196 prefixEnd_6489196 3332076609233498224506737 := by
  unfold tailWord_6489196
  simp only [CollatzResearch.WordTrace]
  refine ⟨118340211099379316644155721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157786948132505755525540961 118340211099379316644155721)
  ·
    refine ⟨88755158324534487483116791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118340211099379316644155721 88755158324534487483116791)
    ·
      refine ⟨133132737486801731224675187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88755158324534487483116791 133132737486801731224675187)
      ·
        refine ⟨199699106230202596837012781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133132737486801731224675187 199699106230202596837012781)
        ·
          refine ⟨74887164836325973813879793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199699106230202596837012781 74887164836325973813879793)
          ·
            refine ⟨56165373627244480360409845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74887164836325973813879793 56165373627244480360409845)
            ·
              refine ⟨5265503777554170033788423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56165373627244480360409845 5265503777554170033788423)
              ·
                refine ⟨7898255666331255050682635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5265503777554170033788423 7898255666331255050682635)
                ·
                  refine ⟨11847383499496882576023953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7898255666331255050682635 11847383499496882576023953)
                  ·
                    refine ⟨8885537624622661932017965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11847383499496882576023953 8885537624622661932017965)
                    ·
                      refine ⟨3332076609233498224506737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8885537624622661932017965 3332076609233498224506737)
                      ·
                        rfl

theorem cell23_6489196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 3].length) (baseStart_6489196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489196 prefixEnd_6489196 := by exact prefixLift 6489196
  have htrace : WordTrace (prefixWord ++ tailWord_6489196) baseStart_6489196 baseEnd_6489196 := by
    simpa [prefixWord, tailWord_6489196, baseEnd_6489196] using wordTrace_append hprefix tailTrace_6489196
  have hstable : (prefixWord ++ tailWord_6489196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489196).length < 2 ^ (prefixWord ++ tailWord_6489196).sum := by decide
  have hdescent : baseEnd_6489196 < baseStart_6489196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489219 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 5, 3, 2]
def baseStart_6489219 : Nat := 118140960795 + 6489219 * 2 ^ 59
def prefixEnd_6489219 : Nat := 4983230072969 + 3 ^ 40 * 6489219 * 2
def baseEnd_6489219 : Nat := 3332088419288551634519131

theorem tailTrace_6489219 : CollatzResearch.WordTrace tailWord_6489219 prefixEnd_6489219 3332088419288551634519131 := by
  unfold tailWord_6489219
  simp only [CollatzResearch.WordTrace]
  refine ⟨236681261077675308216398711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157787507385116872144265807 236681261077675308216398711)
  ·
    refine ⟨355021891616512962324598067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236681261077675308216398711 355021891616512962324598067)
    ·
      refine ⟨532532837424769443486897101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355021891616512962324598067 532532837424769443486897101)
      ·
        refine ⟨199699814034288541307586413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 532532837424769443486897101 199699814034288541307586413)
        ·
          refine ⟨74887430262858202990344905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199699814034288541307586413 74887430262858202990344905)
          ·
            refine ⟨56165572697143652242758679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74887430262858202990344905 56165572697143652242758679)
            ·
              refine ⟨84248359045715478364138019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56165572697143652242758679 84248359045715478364138019)
              ·
                refine ⟨126372538568573217546207029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84248359045715478364138019 126372538568573217546207029)
                ·
                  refine ⟨11847425490803739144956909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126372538568573217546207029 11847425490803739144956909)
                  ·
                    refine ⟨4442784559051402179358841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11847425490803739144956909 4442784559051402179358841)
                    ·
                      refine ⟨3332088419288551634519131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4442784559051402179358841 3332088419288551634519131)
                      ·
                        rfl

theorem cell23_6489219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 3, 2].length) (baseStart_6489219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489219 prefixEnd_6489219 := by exact prefixLift 6489219
  have htrace : WordTrace (prefixWord ++ tailWord_6489219) baseStart_6489219 baseEnd_6489219 := by
    simpa [prefixWord, tailWord_6489219, baseEnd_6489219] using wordTrace_append hprefix tailTrace_6489219
  have hstable : (prefixWord ++ tailWord_6489219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489219).length < 2 ^ (prefixWord ++ tailWord_6489219).sum := by decide
  have hdescent : baseEnd_6489219 < baseStart_6489219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489226 : List Nat := [3, 1, 2, 3, 1, 1, 1, 5, 2, 1, 3]
def baseStart_6489226 : Nat := 118140960795 + 6489226 * 2 ^ 59
def prefixEnd_6489226 : Nat := 4983230072969 + 3 ^ 40 * 6489226 * 2
def baseEnd_6489226 : Nat := 3332092013653133107131599

theorem tailTrace_6489226 : CollatzResearch.WordTrace tailWord_6489226 prefixEnd_6489226 3332092013653133107131599 := by
  unfold tailWord_6489226
  simp only [CollatzResearch.WordTrace]
  refine ⟨59170379097162487102975883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157787677592433298941269021 59170379097162487102975883)
  ·
    refine ⟨88755568645743730654463825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59170379097162487102975883 88755568645743730654463825)
    ·
      refine ⟨66566676484307797990847869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88755568645743730654463825 66566676484307797990847869)
      ·
        refine ⟨24962503681615424246567951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66566676484307797990847869 24962503681615424246567951)
        ·
          refine ⟨37443755522423136369851927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24962503681615424246567951 37443755522423136369851927)
          ·
            refine ⟨56165633283634704554777891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37443755522423136369851927 56165633283634704554777891)
            ·
              refine ⟨84248449925452056832166837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56165633283634704554777891 84248449925452056832166837)
              ·
                refine ⟨7898292180511130328015641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84248449925452056832166837 7898292180511130328015641)
                ·
                  refine ⟨5923719135383347746011731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7898292180511130328015641 5923719135383347746011731)
                  ·
                    refine ⟨8885578703075021619017597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5923719135383347746011731 8885578703075021619017597)
                    ·
                      refine ⟨3332092013653133107131599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8885578703075021619017597 3332092013653133107131599)
                      ·
                        rfl

theorem cell23_6489226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_6489226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489226 prefixEnd_6489226 := by exact prefixLift 6489226
  have htrace : WordTrace (prefixWord ++ tailWord_6489226) baseStart_6489226 baseEnd_6489226 := by
    simpa [prefixWord, tailWord_6489226, baseEnd_6489226] using wordTrace_append hprefix tailTrace_6489226
  have hstable : (prefixWord ++ tailWord_6489226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489226).length < 2 ^ (prefixWord ++ tailWord_6489226).sum := by decide
  have hdescent : baseEnd_6489226 < baseStart_6489226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489253 : List Nat := [1, 3, 1, 2, 1, 4, 4, 1, 1, 3, 2]
def baseStart_6489253 : Nat := 118140960795 + 6489253 * 2 ^ 59
def prefixEnd_6489253 : Nat := 4983230072969 + 3 ^ 40 * 6489253 * 2
def baseEnd_6489253 : Nat := 3332105877630804501493975

theorem tailTrace_6489253 : CollatzResearch.WordTrace tailWord_6489253 prefixEnd_6489253 3332105877630804501493975 := by
  unfold tailWord_6489253
  simp only [CollatzResearch.WordTrace]
  refine ⟨236682501159552132023136413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157788334106368088015424275 236682501159552132023136413)
  ·
    refine ⟨88755937934832049508676155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236682501159552132023136413 88755937934832049508676155)
    ·
      refine ⟨133133906902248074263014233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88755937934832049508676155 133133906902248074263014233)
      ·
        refine ⟨99850430176686055697260675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133133906902248074263014233 99850430176686055697260675)
        ·
          refine ⟨149775645265029083545891013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99850430176686055697260675 149775645265029083545891013)
          ·
            refine ⟨28082933487192953164854565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149775645265029083545891013 28082933487192953164854565)
            ·
              refine ⟨5265550028848678718410231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28082933487192953164854565 5265550028848678718410231)
              ·
                refine ⟨7898325043273018077615347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5265550028848678718410231 7898325043273018077615347)
                ·
                  refine ⟨11847487564909527116423021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7898325043273018077615347 11847487564909527116423021)
                  ·
                    refine ⟨4442807836841072668658633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11847487564909527116423021 4442807836841072668658633)
                    ·
                      refine ⟨3332105877630804501493975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4442807836841072668658633 3332105877630804501493975)
                      ·
                        rfl

theorem cell23_6489253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 1, 3, 2].length) (baseStart_6489253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489253 prefixEnd_6489253 := by exact prefixLift 6489253
  have htrace : WordTrace (prefixWord ++ tailWord_6489253) baseStart_6489253 baseEnd_6489253 := by
    simpa [prefixWord, tailWord_6489253, baseEnd_6489253] using wordTrace_append hprefix tailTrace_6489253
  have hstable : (prefixWord ++ tailWord_6489253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489253).length < 2 ^ (prefixWord ++ tailWord_6489253).sum := by decide
  have hdescent : baseEnd_6489253 < baseStart_6489253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489349 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 5, 4]
def baseStart_6489349 : Nat := 118140960795 + 6489349 * 2 ^ 59
def prefixEnd_6489349 : Nat := 4983230072969 + 3 ^ 40 * 6489349 * 2
def baseEnd_6489349 : Nat := 1110718390591212041964511

theorem tailTrace_6489349 : CollatzResearch.WordTrace tailWord_6489349 prefixEnd_6489349 1110718390591212041964511 := by
  unfold tailWord_6489349
  simp only [CollatzResearch.WordTrace]
  refine ⟨236686002567204340418631101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157790668378136226945754067 236686002567204340418631101)
  ·
    refine ⟨88757250962701627656986663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236686002567204340418631101 88757250962701627656986663)
    ·
      refine ⟨133135876444052441485479995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88757250962701627656986663 133135876444052441485479995)
      ·
        refine ⟨199703814666078662228219993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133135876444052441485479995 199703814666078662228219993)
        ·
          refine ⟨149777860999558996671164995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199703814666078662228219993 149777860999558996671164995)
          ·
            refine ⟨224666791499338495006747493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149777860999558996671164995 224666791499338495006747493)
            ·
              refine ⟨42125023406125967813765155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224666791499338495006747493 42125023406125967813765155)
              ·
                refine ⟨63187535109188951720647733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42125023406125967813765155 63187535109188951720647733)
                ·
                  refine ⟨5923831416486464223810725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63187535109188951720647733 5923831416486464223810725)
                  ·
                    refine ⟨1110718390591212041964511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5923831416486464223810725 1110718390591212041964511)
                    ·
                      rfl

theorem cell23_6489349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 5, 4].length) (baseStart_6489349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489349 prefixEnd_6489349 := by exact prefixLift 6489349
  have htrace : WordTrace (prefixWord ++ tailWord_6489349) baseStart_6489349 baseEnd_6489349 := by
    simpa [prefixWord, tailWord_6489349, baseEnd_6489349] using wordTrace_append hprefix tailTrace_6489349
  have hstable : (prefixWord ++ tailWord_6489349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489349).length < 2 ^ (prefixWord ++ tailWord_6489349).sum := by decide
  have hdescent : baseEnd_6489349 < baseStart_6489349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489356 : List Nat := [2, 2, 1, 2, 2, 4, 2, 1, 2, 1, 4]
def baseStart_6489356 : Nat := 118140960795 + 6489356 * 2 ^ 59
def prefixEnd_6489356 : Nat := 4983230072969 + 3 ^ 40 * 6489356 * 2
def baseEnd_6489356 : Nat := 3332158766138217598506001

theorem tailTrace_6489356 : CollatzResearch.WordTrace tailWord_6489356 prefixEnd_6489356 3332158766138217598506001 := by
  unfold tailWord_6489356
  simp only [CollatzResearch.WordTrace]
  refine ⟨118343128939089490307067961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157790838585452653742757281 118343128939089490307067961)
  ·
    refine ⟨88757346704317117730300971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118343128939089490307067961 88757346704317117730300971)
    ·
      refine ⟨133136020056475676595451457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88757346704317117730300971 133136020056475676595451457)
      ·
        refine ⟨99852015042356757446588593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133136020056475676595451457 99852015042356757446588593)
        ·
          refine ⟨74889011281767568084941445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99852015042356757446588593 74889011281767568084941445)
          ·
            refine ⟨14041689615331419015926521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74889011281767568084941445 14041689615331419015926521)
            ·
              refine ⟨10531267211498564261944891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14041689615331419015926521 10531267211498564261944891)
              ·
                refine ⟨15796900817247846392917337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10531267211498564261944891 15796900817247846392917337)
                ·
                  refine ⟨11847675612935884794688003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15796900817247846392917337 11847675612935884794688003)
                  ·
                    refine ⟨17771513419403827192032005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11847675612935884794688003 17771513419403827192032005)
                    ·
                      refine ⟨3332158766138217598506001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17771513419403827192032005 3332158766138217598506001)
                      ·
                        rfl

theorem cell23_6489356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_6489356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489356 prefixEnd_6489356 := by exact prefixLift 6489356
  have htrace : WordTrace (prefixWord ++ tailWord_6489356) baseStart_6489356 baseEnd_6489356 := by
    simpa [prefixWord, tailWord_6489356, baseEnd_6489356] using wordTrace_append hprefix tailTrace_6489356
  have hstable : (prefixWord ++ tailWord_6489356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489356).length < 2 ^ (prefixWord ++ tailWord_6489356).sum := by decide
  have hdescent : baseEnd_6489356 < baseStart_6489356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489374 : List Nat := [4, 3, 2, 1, 3, 1, 2, 2, 5]
def baseStart_6489374 : Nat := 118140960795 + 6489374 * 2 ^ 59
def prefixEnd_6489374 : Nat := 4983230072969 + 3 ^ 40 * 6489374 * 2
def baseEnd_6489374 : Nat := 370240889865555392008991

theorem tailTrace_6489374 : CollatzResearch.WordTrace tailWord_6489374 prefixEnd_6489374 370240889865555392008991 := by
  unfold tailWord_6489374
  simp only [CollatzResearch.WordTrace]
  refine ⟨29585864299014221211036397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157791276261409179792194117 29585864299014221211036397)
  ·
    refine ⟨11094699112130332954138649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29585864299014221211036397 11094699112130332954138649)
    ·
      refine ⟨8321024334097749715603987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11094699112130332954138649 8321024334097749715603987)
      ·
        refine ⟨12481536501146624573405981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8321024334097749715603987 12481536501146624573405981)
        ·
          refine ⟨4680576187929984215027243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12481536501146624573405981 4680576187929984215027243)
          ·
            refine ⟨7020864281894976322540865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680576187929984215027243 7020864281894976322540865)
            ·
              refine ⟨5265648211421232241905649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7020864281894976322540865 5265648211421232241905649)
              ·
                refine ⟨3949236158565924181429237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5265648211421232241905649 3949236158565924181429237)
                ·
                  refine ⟨370240889865555392008991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3949236158565924181429237 370240889865555392008991)
                  ·
                    rfl

theorem cell23_6489374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_6489374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489374 prefixEnd_6489374 := by exact prefixLift 6489374
  have htrace : WordTrace (prefixWord ++ tailWord_6489374) baseStart_6489374 baseEnd_6489374 := by
    simpa [prefixWord, tailWord_6489374, baseEnd_6489374] using wordTrace_append hprefix tailTrace_6489374
  have hstable : (prefixWord ++ tailWord_6489374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489374).length < 2 ^ (prefixWord ++ tailWord_6489374).sum := by decide
  have hdescent : baseEnd_6489374 < baseStart_6489374 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489379 : List Nat := [1, 1, 1, 4, 2, 3, 1, 4, 6]
def baseStart_6489379 : Nat := 118140960795 + 6489379 * 2 ^ 59
def prefixEnd_6489379 : Nat := 4983230072969 + 3 ^ 40 * 6489379 * 2
def baseEnd_6489379 : Nat := 370241175132585667613155

theorem tailTrace_6489379 : CollatzResearch.WordTrace tailWord_6489379 prefixEnd_6489379 370241175132585667613155 := by
  unfold tailWord_6489379
  simp only [CollatzResearch.WordTrace]
  refine ⟨236687096757095655542223191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157791397838063770361482127 236687096757095655542223191)
  ·
    refine ⟨355030645135643483313334787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236687096757095655542223191 355030645135643483313334787)
    ·
      refine ⟨532545967703465224970002181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355030645135643483313334787 532545967703465224970002181)
      ·
        refine ⟨99852368944399729681875409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 532545967703465224970002181 99852368944399729681875409)
        ·
          refine ⟨74889276708299797261406557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99852368944399729681875409 74889276708299797261406557)
          ·
            refine ⟨28083478765612423973027459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74889276708299797261406557 28083478765612423973027459)
            ·
              refine ⟨42125218148418635959541189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28083478765612423973027459 42125218148418635959541189)
              ·
                refine ⟨7898478402828494242413973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42125218148418635959541189 7898478402828494242413973)
                ·
                  refine ⟨370241175132585667613155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7898478402828494242413973 370241175132585667613155)
                  ·
                    rfl

theorem cell23_6489379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 6].length) (baseStart_6489379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489379 prefixEnd_6489379 := by exact prefixLift 6489379
  have htrace : WordTrace (prefixWord ++ tailWord_6489379) baseStart_6489379 baseEnd_6489379 := by
    simpa [prefixWord, tailWord_6489379, baseEnd_6489379] using wordTrace_append hprefix tailTrace_6489379
  have hstable : (prefixWord ++ tailWord_6489379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489379).length < 2 ^ (prefixWord ++ tailWord_6489379).sum := by decide
  have hdescent : baseEnd_6489379 < baseStart_6489379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489396 : List Nat := [2, 5, 1, 1, 1, 1, 1, 5, 6]
def baseStart_6489396 : Nat := 118140960795 + 6489396 * 2 ^ 59
def prefixEnd_6489396 : Nat := 4983230072969 + 3 ^ 40 * 6489396 * 2
def baseEnd_6489396 : Nat := 370242145040488604667313

theorem tailTrace_6489396 : CollatzResearch.WordTrace tailWord_6489396 prefixEnd_6489396 370242145040488604667313 := by
  unfold tailWord_6489396
  simp only [CollatzResearch.WordTrace]
  refine ⟨118343858399017033722796021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157791811198689378297061361 118343858399017033722796021)
  ·
    refine ⟨11094736724907846911512127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118343858399017033722796021 11094736724907846911512127)
    ·
      refine ⟨16642105087361770367268191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11094736724907846911512127 16642105087361770367268191)
      ·
        refine ⟨24963157631042655550902287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16642105087361770367268191 24963157631042655550902287)
        ·
          refine ⟨37444736446563983326353431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24963157631042655550902287 37444736446563983326353431)
          ·
            refine ⟨56167104669845974989530147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37444736446563983326353431 56167104669845974989530147)
            ·
              refine ⟨84250657004768962484295221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56167104669845974989530147 84250657004768962484295221)
              ·
                refine ⟨7898499094197090232902677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84250657004768962484295221 7898499094197090232902677)
                ·
                  refine ⟨370242145040488604667313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7898499094197090232902677 370242145040488604667313)
                  ·
                    rfl

theorem cell23_6489396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_6489396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489396 prefixEnd_6489396 := by exact prefixLift 6489396
  have htrace : WordTrace (prefixWord ++ tailWord_6489396) baseStart_6489396 baseEnd_6489396 := by
    simpa [prefixWord, tailWord_6489396, baseEnd_6489396] using wordTrace_append hprefix tailTrace_6489396
  have hstable : (prefixWord ++ tailWord_6489396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489396).length < 2 ^ (prefixWord ++ tailWord_6489396).sum := by decide
  have hdescent : baseEnd_6489396 < baseStart_6489396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489440 : List Nat := [2, 1, 1, 3, 4, 1, 2, 4, 1, 1, 3]
def baseStart_6489440 : Nat := 118140960795 + 6489440 * 2 ^ 59
def prefixEnd_6489440 : Nat := 4983230072969 + 3 ^ 40 * 6489440 * 2
def baseEnd_6489440 : Nat := 3332201898513195269855615

theorem tailTrace_6489440 : CollatzResearch.WordTrace tailWord_6489440 prefixEnd_6489440 3332201898513195269855615 := by
  unfold tailWord_6489440
  simp only [CollatzResearch.WordTrace]
  refine ⟨118344660804937331480096887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157792881073249775306795849 118344660804937331480096887)
  ·
    refine ⟨177516991207405997220145331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118344660804937331480096887 177516991207405997220145331)
    ·
      refine ⟨266275486811108995830217997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177516991207405997220145331 266275486811108995830217997)
      ·
        refine ⟨99853307554165873436331749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266275486811108995830217997 99853307554165873436331749)
        ·
          refine ⟨18722495166406101269312203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99853307554165873436331749 18722495166406101269312203)
          ·
            refine ⟨28083742749609151903968305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18722495166406101269312203 28083742749609151903968305)
            ·
              refine ⟨21062807062206863927976229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28083742749609151903968305 21062807062206863927976229)
              ·
                refine ⟨3949276324163786986495543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21062807062206863927976229 3949276324163786986495543)
                ·
                  refine ⟨5923914486245680479743315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3949276324163786986495543 5923914486245680479743315)
                  ·
                    refine ⟨8885871729368520719614973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5923914486245680479743315 8885871729368520719614973)
                    ·
                      refine ⟨3332201898513195269855615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8885871729368520719614973 3332201898513195269855615)
                      ·
                        rfl

theorem cell23_6489440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 1, 1, 3].length) (baseStart_6489440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489440 prefixEnd_6489440 := by exact prefixLift 6489440
  have htrace : WordTrace (prefixWord ++ tailWord_6489440) baseStart_6489440 baseEnd_6489440 := by
    simpa [prefixWord, tailWord_6489440, baseEnd_6489440] using wordTrace_append hprefix tailTrace_6489440
  have hstable : (prefixWord ++ tailWord_6489440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489440).length < 2 ^ (prefixWord ++ tailWord_6489440).sum := by decide
  have hdescent : baseEnd_6489440 < baseStart_6489440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489449 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 2, 6, 3]
def baseStart_6489449 : Nat := 118140960795 + 6489449 * 2 ^ 59
def prefixEnd_6489449 : Nat := 4983230072969 + 3 ^ 40 * 6489449 * 2
def baseEnd_6489449 : Nat := 3332206519839085734643073

theorem tailTrace_6489449 : CollatzResearch.WordTrace tailWord_6489449 prefixEnd_6489449 3332206519839085734643073 := by
  unfold tailWord_6489449
  simp only [CollatzResearch.WordTrace]
  refine ⟨236689649866842057497271401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157793099911228038331514267 236689649866842057497271401)
  ·
    refine ⟨177517237400131543122953551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236689649866842057497271401 177517237400131543122953551)
    ·
      refine ⟨266275856100197314684430327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177517237400131543122953551 266275856100197314684430327)
      ·
        refine ⟨399413784150295972026645491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266275856100197314684430327 399413784150295972026645491)
        ·
          refine ⟨599120676225443958039968237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399413784150295972026645491 599120676225443958039968237)
          ·
            refine ⟨224670253584541484264988089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 599120676225443958039968237 224670253584541484264988089)
            ·
              refine ⟨168502690188406113198741067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224670253584541484264988089 168502690188406113198741067)
              ·
                refine ⟨252754035282609169798111601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168502690188406113198741067 252754035282609169798111601)
                ·
                  refine ⟨189565526461956877348583701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252754035282609169798111601 189565526461956877348583701)
                  ·
                    refine ⟨8885884052904228625714861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 189565526461956877348583701 8885884052904228625714861)
                    ·
                      refine ⟨3332206519839085734643073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8885884052904228625714861 3332206519839085734643073)
                      ·
                        rfl

theorem cell23_6489449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 6, 3].length) (baseStart_6489449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489449 prefixEnd_6489449 := by exact prefixLift 6489449
  have htrace : WordTrace (prefixWord ++ tailWord_6489449) baseStart_6489449 baseEnd_6489449 := by
    simpa [prefixWord, tailWord_6489449, baseEnd_6489449] using wordTrace_append hprefix tailTrace_6489449
  have hstable : (prefixWord ++ tailWord_6489449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489449).length < 2 ^ (prefixWord ++ tailWord_6489449).sum := by decide
  have hdescent : baseEnd_6489449 < baseStart_6489449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489463 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 3, 2, 2]
def baseStart_6489463 : Nat := 118140960795 + 6489463 * 2 ^ 59
def prefixEnd_6489463 : Nat := 4983230072969 + 3 ^ 40 * 6489463 * 2
def baseEnd_6489463 : Nat := 3332213708568248679868009

theorem tailTrace_6489463 : CollatzResearch.WordTrace tailWord_6489463 prefixEnd_6489463 3332213708568248679868009 := by
  unfold tailWord_6489463
  simp only [CollatzResearch.WordTrace]
  refine ⟨236690160488791337888281043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157793440325860891925520695 236690160488791337888281043)
  ·
    refine ⟨355035240733187006832421565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236690160488791337888281043 355035240733187006832421565)
    ·
      refine ⟨133138215274945127562158087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355035240733187006832421565 133138215274945127562158087)
      ·
        refine ⟨199707322912417691343237131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133138215274945127562158087 199707322912417691343237131)
        ·
          refine ⟨299560984368626537014855697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199707322912417691343237131 299560984368626537014855697)
          ·
            refine ⟨224670738276469902761141773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299560984368626537014855697 224670738276469902761141773)
            ·
              refine ⟨84251526853676213535428165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224670738276469902761141773 84251526853676213535428165)
              ·
                refine ⟨15797161285064290037892781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84251526853676213535428165 15797161285064290037892781)
                ·
                  refine ⟨5923935481899108764209793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15797161285064290037892781 5923935481899108764209793)
                  ·
                    refine ⟨4442951611424331573157345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5923935481899108764209793 4442951611424331573157345)
                    ·
                      refine ⟨3332213708568248679868009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4442951611424331573157345 3332213708568248679868009)
                      ·
                        rfl

theorem cell23_6489463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 2, 2].length) (baseStart_6489463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489463 prefixEnd_6489463 := by exact prefixLift 6489463
  have htrace : WordTrace (prefixWord ++ tailWord_6489463) baseStart_6489463 baseEnd_6489463 := by
    simpa [prefixWord, tailWord_6489463, baseEnd_6489463] using wordTrace_append hprefix tailTrace_6489463
  have hstable : (prefixWord ++ tailWord_6489463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489463).length < 2 ^ (prefixWord ++ tailWord_6489463).sum := by decide
  have hdescent : baseEnd_6489463 < baseStart_6489463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489469 : List Nat := [1, 4, 1, 1, 2, 2, 3, 9]
def baseStart_6489469 : Nat := 118140960795 + 6489469 * 2 ^ 59
def prefixEnd_6489469 : Nat := 4983230072969 + 3 ^ 40 * 6489469 * 2
def baseEnd_6489469 : Nat := 123415436646376876162703

theorem tailTrace_6489469 : CollatzResearch.WordTrace tailWord_6489469 prefixEnd_6489469 123415436646376876162703 := by
  unfold tailWord_6489469
  simp only [CollatzResearch.WordTrace]
  refine ⟨236690379326769600912999461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157793586217846400608666307 236690379326769600912999461)
  ·
    refine ⟨44379446123769300171187399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236690379326769600912999461 44379446123769300171187399)
    ·
      refine ⟨66569169185653950256781099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44379446123769300171187399 66569169185653950256781099)
      ·
        refine ⟨99853753778480925385171649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66569169185653950256781099 99853753778480925385171649)
        ·
          refine ⟨74890315333860694038878737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99853753778480925385171649 74890315333860694038878737)
          ·
            refine ⟨56167736500395520529159053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74890315333860694038878737 56167736500395520529159053)
            ·
              refine ⟨21062901187648320198434645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56167736500395520529159053 21062901187648320198434645)
              ·
                refine ⟨123415436646376876162703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21062901187648320198434645 123415436646376876162703)
                ·
                  rfl

theorem cell23_6489469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 9].length) (baseStart_6489469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489469 prefixEnd_6489469 := by exact prefixLift 6489469
  have htrace : WordTrace (prefixWord ++ tailWord_6489469) baseStart_6489469 baseEnd_6489469 := by
    simpa [prefixWord, tailWord_6489469, baseEnd_6489469] using wordTrace_append hprefix tailTrace_6489469
  have hstable : (prefixWord ++ tailWord_6489469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489469).length < 2 ^ (prefixWord ++ tailWord_6489469).sum := by decide
  have hdescent : baseEnd_6489469 < baseStart_6489469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489474 : List Nat := [3, 4, 2, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_6489474 : Nat := 118140960795 + 6489474 * 2 ^ 59
def prefixEnd_6489474 : Nat := 4983230072969 + 3 ^ 40 * 6489474 * 2
def baseEnd_6489474 : Nat := 3332219356855448136830459

theorem tailTrace_6489474 : CollatzResearch.WordTrace tailWord_6489474 prefixEnd_6489474 3332219356855448136830459 := by
  unfold tailWord_6489474
  simp only [CollatzResearch.WordTrace]
  refine ⟨59172640422937871691732869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157793707794500991177954317 59172640422937871691732869)
  ·
    refine ⟨11094870079300850942199913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59172640422937871691732869 11094870079300850942199913)
    ·
      refine ⟨8321152559475638206649935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11094870079300850942199913 8321152559475638206649935)
      ·
        refine ⟨12481728839213457309974903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8321152559475638206649935 12481728839213457309974903)
        ·
          refine ⟨18722593258820185964962355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12481728839213457309974903 18722593258820185964962355)
          ·
            refine ⟨28083889888230278947443533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18722593258820185964962355 28083889888230278947443533)
            ·
              refine ⟨10531458708086354605291325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28083889888230278947443533 10531458708086354605291325)
              ·
                refine ⟨3949297015532382976984247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10531458708086354605291325 3949297015532382976984247)
                ·
                  refine ⟨5923945523298574465476371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3949297015532382976984247 5923945523298574465476371)
                  ·
                    refine ⟨8885918284947861698214557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5923945523298574465476371 8885918284947861698214557)
                    ·
                      refine ⟨3332219356855448136830459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8885918284947861698214557 3332219356855448136830459)
                      ·
                        rfl

theorem cell23_6489474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_6489474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489474 prefixEnd_6489474 := by exact prefixLift 6489474
  have htrace : WordTrace (prefixWord ++ tailWord_6489474) baseStart_6489474 baseEnd_6489474 := by
    simpa [prefixWord, tailWord_6489474, baseEnd_6489474] using wordTrace_append hprefix tailTrace_6489474
  have hstable : (prefixWord ++ tailWord_6489474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489474).length < 2 ^ (prefixWord ++ tailWord_6489474).sum := by decide
  have hdescent : baseEnd_6489474 < baseStart_6489474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489509 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 1, 4, 5]
def baseStart_6489509 : Nat := 118140960795 + 6489509 * 2 ^ 59
def prefixEnd_6489509 : Nat := 4983230072969 + 3 ^ 40 * 6489509 * 2
def baseEnd_6489509 : Nat := 3332237328678355499892797

theorem tailTrace_6489509 : CollatzResearch.WordTrace tailWord_6489509 prefixEnd_6489509 3332237328678355499892797 := by
  unfold tailWord_6489509
  simp only [CollatzResearch.WordTrace]
  refine ⟨236691838246624687744455581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157794558831083125162970387 236691838246624687744455581)
  ·
    refine ⟨88759439342484257904170843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236691838246624687744455581 88759439342484257904170843)
    ·
      refine ⟨133139159013726386856256265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88759439342484257904170843 133139159013726386856256265)
      ·
        refine ⟨99854369260294790142192199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133139159013726386856256265 99854369260294790142192199)
        ·
          refine ⟨149781553890442185213288299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99854369260294790142192199 149781553890442185213288299)
          ·
            refine ⟨224672330835663277819932449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149781553890442185213288299 224672330835663277819932449)
            ·
              refine ⟨168504248126747458364949337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224672330835663277819932449 168504248126747458364949337)
              ·
                refine ⟨126378186095060593773712003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168504248126747458364949337 126378186095060593773712003)
                ·
                  refine ⟨189567279142590890660568005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126378186095060593773712003 189567279142590890660568005)
                  ·
                    refine ⟨35543864839235791998856501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 189567279142590890660568005 35543864839235791998856501)
                    ·
                      refine ⟨3332237328678355499892797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35543864839235791998856501 3332237328678355499892797)
                      ·
                        rfl

theorem cell23_6489509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_6489509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489509 prefixEnd_6489509 := by exact prefixLift 6489509
  have htrace : WordTrace (prefixWord ++ tailWord_6489509) baseStart_6489509 baseEnd_6489509 := by
    simpa [prefixWord, tailWord_6489509, baseEnd_6489509] using wordTrace_append hprefix tailTrace_6489509
  have hstable : (prefixWord ++ tailWord_6489509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489509).length < 2 ^ (prefixWord ++ tailWord_6489509).sum := by decide
  have hdescent : baseEnd_6489509 < baseStart_6489509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489517 : List Nat := [1, 5, 2, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_6489517 : Nat := 118140960795 + 6489517 * 2 ^ 59
def prefixEnd_6489517 : Nat := 4983230072969 + 3 ^ 40 * 6489517 * 2
def baseEnd_6489517 : Nat := 3332241436523591468592761

theorem tailTrace_6489517 : CollatzResearch.WordTrace tailWord_6489517 prefixEnd_6489517 3332241436523591468592761 := by
  unfold tailWord_6489517
  simp only [CollatzResearch.WordTrace]
  refine ⟨236692130030595705110746805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157794753353730470073831203 236692130030595705110746805)
  ·
    refine ⟨22189887190368347354132513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 236692130030595705110746805 22189887190368347354132513)
    ·
      refine ⟨16642415392776260515599385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22189887190368347354132513 16642415392776260515599385)
      ·
        refine ⟨12481811544582195386699539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16642415392776260515599385 12481811544582195386699539)
        ·
          refine ⟨18722717316873293080049309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12481811544582195386699539 18722717316873293080049309)
          ·
            refine ⟨7021018993827484905018491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18722717316873293080049309 7021018993827484905018491)
            ·
              refine ⟨10531528490741227357527737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7021018993827484905018491 10531528490741227357527737)
              ·
                refine ⟨7898646368055920518145803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10531528490741227357527737 7898646368055920518145803)
                ·
                  refine ⟨11847969552083880777218705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7898646368055920518145803 11847969552083880777218705)
                  ·
                    refine ⟨8885977164062910582914029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11847969552083880777218705 8885977164062910582914029)
                    ·
                      refine ⟨3332241436523591468592761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8885977164062910582914029 3332241436523591468592761)
                      ·
                        rfl

theorem cell23_6489517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_6489517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489517 prefixEnd_6489517 := by exact prefixLift 6489517
  have htrace : WordTrace (prefixWord ++ tailWord_6489517) baseStart_6489517 baseEnd_6489517 := by
    simpa [prefixWord, tailWord_6489517, baseEnd_6489517] using wordTrace_append hprefix tailTrace_6489517
  have hstable : (prefixWord ++ tailWord_6489517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489517).length < 2 ^ (prefixWord ++ tailWord_6489517).sum := by decide
  have hdescent : baseEnd_6489517 < baseStart_6489517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489559 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 11]
def baseStart_6489559 : Nat := 118140960795 + 6489559 * 2 ^ 59
def prefixEnd_6489559 : Nat := 4983230072969 + 3 ^ 40 * 6489559 * 2
def baseEnd_6489559 : Nat := 370251444745675589363063

theorem tailTrace_6489559 : CollatzResearch.WordTrace tailWord_6489559 prefixEnd_6489559 370251444745675589363063 := by
  unfold tailWord_6489559
  simp only [CollatzResearch.WordTrace]
  refine ⟨236693661896443546283775731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157795774597629030855850487 236693661896443546283775731)
  ·
    refine ⟨355040492844665319425663597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236693661896443546283775731 355040492844665319425663597)
    ·
      refine ⟨133140184816749494784623849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355040492844665319425663597 133140184816749494784623849)
      ·
        refine ⟨99855138612562121088467887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133140184816749494784623849 99855138612562121088467887)
        ·
          refine ⟨149782707918843181632701831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99855138612562121088467887 149782707918843181632701831)
          ·
            refine ⟨224674061878264772449052747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149782707918843181632701831 224674061878264772449052747)
            ·
              refine ⟨337011092817397158673579121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224674061878264772449052747 337011092817397158673579121)
              ·
                refine ⟨252758319613047869005184341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337011092817397158673579121 252758319613047869005184341)
                ·
                  refine ⟨370251444745675589363063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 252758319613047869005184341 370251444745675589363063)
                  ·
                    rfl

theorem cell23_6489559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 11].length) (baseStart_6489559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489559 prefixEnd_6489559 := by exact prefixLift 6489559
  have htrace : WordTrace (prefixWord ++ tailWord_6489559) baseStart_6489559 baseEnd_6489559 := by
    simpa [prefixWord, tailWord_6489559, baseEnd_6489559] using wordTrace_append hprefix tailTrace_6489559
  have hstable : (prefixWord ++ tailWord_6489559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489559).length < 2 ^ (prefixWord ++ tailWord_6489559).sum := by decide
  have hdescent : baseEnd_6489559 < baseStart_6489559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489576 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 7]
def baseStart_6489576 : Nat := 118140960795 + 6489576 * 2 ^ 59
def prefixEnd_6489576 : Nat := 4983230072969 + 3 ^ 40 * 6489576 * 2
def baseEnd_6489576 : Nat := 370252414653578526417221

theorem tailTrace_6489576 : CollatzResearch.WordTrace tailWord_6489576 prefixEnd_6489576 370252414653578526417221 := by
  unfold tailWord_6489576
  simp only [CollatzResearch.WordTrace]
  refine ⟨118347140968690979093572291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157796187958254638791429721 118347140968690979093572291)
  ·
    refine ⟨177520711453036468640358437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118347140968690979093572291 177520711453036468640358437)
    ·
      refine ⟨33285133397444337870067207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177520711453036468640358437 33285133397444337870067207)
      ·
        refine ⟨49927700096166506805100811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33285133397444337870067207 49927700096166506805100811)
        ·
          refine ⟨74891550144249760207651217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49927700096166506805100811 74891550144249760207651217)
          ·
            refine ⟨56168662608187320155738413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74891550144249760207651217 56168662608187320155738413)
            ·
              refine ⟨21063248478070245058401905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56168662608187320155738413 21063248478070245058401905)
              ·
                refine ⟨15797436358552683793801429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21063248478070245058401905 15797436358552683793801429)
                ·
                  refine ⟨370252414653578526417221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15797436358552683793801429 370252414653578526417221)
                  ·
                    rfl

theorem cell23_6489576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 7].length) (baseStart_6489576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489576 prefixEnd_6489576 := by exact prefixLift 6489576
  have htrace : WordTrace (prefixWord ++ tailWord_6489576) baseStart_6489576 baseEnd_6489576 := by
    simpa [prefixWord, tailWord_6489576, baseEnd_6489576] using wordTrace_append hprefix tailTrace_6489576
  have hstable : (prefixWord ++ tailWord_6489576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489576).length < 2 ^ (prefixWord ++ tailWord_6489576).sum := by decide
  have hdescent : baseEnd_6489576 < baseStart_6489576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489660 : List Nat := [2, 2, 2, 2, 4, 1, 1, 2, 2, 1, 4]
def baseStart_6489660 : Nat := 118140960795 + 6489660 * 2 ^ 59
def prefixEnd_6489660 : Nat := 4983230072969 + 3 ^ 40 * 6489660 * 2
def baseEnd_6489660 : Nat := 3332314864257184409104603

theorem tailTrace_6489660 : CollatzResearch.WordTrace tailWord_6489660 prefixEnd_6489660 3332314864257184409104603 := by
  unfold tailWord_6489660
  simp only [CollatzResearch.WordTrace]
  refine ⟨118348672834538820266601217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157798230446051760355468289 118348672834538820266601217)
  ·
    refine ⟨88761504625904115199950913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118348672834538820266601217 88761504625904115199950913)
    ·
      refine ⟨66571128469428086399963185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88761504625904115199950913 66571128469428086399963185)
      ·
        refine ⟨49928346352071064799972389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66571128469428086399963185 49928346352071064799972389)
        ·
          refine ⟨9361564941013324649994823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49928346352071064799972389 9361564941013324649994823)
          ·
            refine ⟨14042347411519986974992235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9361564941013324649994823 14042347411519986974992235)
            ·
              refine ⟨21063521117279980462488353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14042347411519986974992235 21063521117279980462488353)
              ·
                refine ⟨15797640837959985346866265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21063521117279980462488353 15797640837959985346866265)
                ·
                  refine ⟨11848230628469989010149699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15797640837959985346866265 11848230628469989010149699)
                  ·
                    refine ⟨17772345942704983515224549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11848230628469989010149699 17772345942704983515224549)
                    ·
                      refine ⟨3332314864257184409104603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17772345942704983515224549 3332314864257184409104603)
                      ·
                        rfl

theorem cell23_6489660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_6489660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489660 prefixEnd_6489660 := by exact prefixLift 6489660
  have htrace : WordTrace (prefixWord ++ tailWord_6489660) baseStart_6489660 baseEnd_6489660 := by
    simpa [prefixWord, tailWord_6489660, baseEnd_6489660] using wordTrace_append hprefix tailTrace_6489660
  have hstable : (prefixWord ++ tailWord_6489660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489660).length < 2 ^ (prefixWord ++ tailWord_6489660).sum := by decide
  have hdescent : baseEnd_6489660 < baseStart_6489660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489663 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 3]
def baseStart_6489663 : Nat := 118140960795 + 6489663 * 2 ^ 59
def prefixEnd_6489663 : Nat := 4983230072969 + 3 ^ 40 * 6489663 * 2
def baseEnd_6489663 : Nat := 3332316404699147897367089

theorem tailTrace_6489663 : CollatzResearch.WordTrace tailWord_6489663 prefixEnd_6489663 3332316404699147897367089 := by
  unfold tailWord_6489663
  simp only [CollatzResearch.WordTrace]
  refine ⟨236697455088066772045561643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157798303392044514697041095 236697455088066772045561643)
  ·
    refine ⟨355046182632100158068342465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236697455088066772045561643 355046182632100158068342465)
    ·
      refine ⟨266284636974075118551256849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355046182632100158068342465 266284636974075118551256849)
      ·
        refine ⟨199713477730556338913442637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266284636974075118551256849 199713477730556338913442637)
        ·
          refine ⟨74892554148958627092540989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199713477730556338913442637 74892554148958627092540989)
          ·
            refine ⟨28084707805859485159702871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74892554148958627092540989 28084707805859485159702871)
            ·
              refine ⟨42127061708789227739554307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28084707805859485159702871 42127061708789227739554307)
              ·
                refine ⟨63190592563183841609331461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42127061708789227739554307 63190592563183841609331461)
                ·
                  refine ⟨11848236105596970301749649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63190592563183841609331461 11848236105596970301749649)
                  ·
                    refine ⟨8886177079197727726312237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11848236105596970301749649 8886177079197727726312237)
                    ·
                      refine ⟨3332316404699147897367089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8886177079197727726312237 3332316404699147897367089)
                      ·
                        rfl

theorem cell23_6489663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 3].length) (baseStart_6489663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489663 prefixEnd_6489663 := by exact prefixLift 6489663
  have htrace : WordTrace (prefixWord ++ tailWord_6489663) baseStart_6489663 baseEnd_6489663 := by
    simpa [prefixWord, tailWord_6489663, baseEnd_6489663] using wordTrace_append hprefix tailTrace_6489663
  have hstable : (prefixWord ++ tailWord_6489663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489663).length < 2 ^ (prefixWord ++ tailWord_6489663).sum := by decide
  have hdescent : baseEnd_6489663 < baseStart_6489663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489713 : List Nat := [1, 2, 2, 2, 1, 1, 1, 7, 1, 5]
def baseStart_6489713 : Nat := 118140960795 + 6489713 * 2 ^ 59
def prefixEnd_6489713 : Nat := 4983230072969 + 3 ^ 40 * 6489713 * 2
def baseEnd_6489713 : Nat := 1110780692910624233913953

theorem tailTrace_6489713 : CollatzResearch.WordTrace tailWord_6489713 prefixEnd_6489713 1110780692910624233913953 := by
  unfold tailWord_6489713
  simp only [CollatzResearch.WordTrace]
  refine ⟨236699278737885630584881793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157799519158590420389921195 236699278737885630584881793)
  ·
    refine ⟨177524459053414222938661345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236699278737885630584881793 177524459053414222938661345)
    ·
      refine ⟨133143344290060667203996009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177524459053414222938661345 133143344290060667203996009)
      ·
        refine ⟨99857508217545500402997007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133143344290060667203996009 99857508217545500402997007)
        ·
          refine ⟨149786262326318250604495511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99857508217545500402997007 149786262326318250604495511)
          ·
            refine ⟨224679393489477375906743267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149786262326318250604495511 224679393489477375906743267)
            ·
              refine ⟨337019090234216063860114901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224679393489477375906743267 337019090234216063860114901)
              ·
                refine ⟨7898884927364438996721443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 337019090234216063860114901 7898884927364438996721443)
                ·
                  refine ⟨11848327391046658495082165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7898884927364438996721443 11848327391046658495082165)
                  ·
                    refine ⟨1110780692910624233913953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11848327391046658495082165 1110780692910624233913953)
                    ·
                      rfl

theorem cell23_6489713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_6489713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489713 prefixEnd_6489713 := by exact prefixLift 6489713
  have htrace : WordTrace (prefixWord ++ tailWord_6489713) baseStart_6489713 baseEnd_6489713 := by
    simpa [prefixWord, tailWord_6489713, baseEnd_6489713] using wordTrace_append hprefix tailTrace_6489713
  have hstable : (prefixWord ++ tailWord_6489713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489713).length < 2 ^ (prefixWord ++ tailWord_6489713).sum := by decide
  have hdescent : baseEnd_6489713 < baseStart_6489713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489733 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 5, 1, 4]
def baseStart_6489733 : Nat := 118140960795 + 6489733 * 2 ^ 59
def prefixEnd_6489733 : Nat := 4983230072969 + 3 ^ 40 * 6489733 * 2
def baseEnd_6489733 : Nat := 3332352348344962623491767

theorem tailTrace_6489733 : CollatzResearch.WordTrace tailWord_6489733 prefixEnd_6489733 3332352348344962623491767 := by
  unfold tailWord_6489733
  simp only [CollatzResearch.WordTrace]
  refine ⟨236700008197813174000609853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157800005465208782667073235 236700008197813174000609853)
  ·
    refine ⟨88762503074179940250228695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236700008197813174000609853 88762503074179940250228695)
    ·
      refine ⟨133143754611269910375343043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88762503074179940250228695 133143754611269910375343043)
      ·
        refine ⟨199715631916904865563014565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133143754611269910375343043 199715631916904865563014565)
        ·
          refine ⟨37446680984419662293065231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199715631916904865563014565 37446680984419662293065231)
          ·
            refine ⟨56170021476629493439597847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37446680984419662293065231 56170021476629493439597847)
            ·
              refine ⟨84255032214944240159396771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56170021476629493439597847 84255032214944240159396771)
              ·
                refine ⟨126382548322416360239095157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84255032214944240159396771 126382548322416360239095157)
                ·
                  refine ⟨11848363905226533772415171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126382548322416360239095157 11848363905226533772415171)
                  ·
                    refine ⟨17772545857839800658622757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11848363905226533772415171 17772545857839800658622757)
                    ·
                      refine ⟨3332352348344962623491767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17772545857839800658622757 3332352348344962623491767)
                      ·
                        rfl

theorem cell23_6489733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_6489733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489733 prefixEnd_6489733 := by exact prefixLift 6489733
  have htrace : WordTrace (prefixWord ++ tailWord_6489733) baseStart_6489733 baseEnd_6489733 := by
    simpa [prefixWord, tailWord_6489733, baseEnd_6489733] using wordTrace_append hprefix tailTrace_6489733
  have hstable : (prefixWord ++ tailWord_6489733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489733).length < 2 ^ (prefixWord ++ tailWord_6489733).sum := by decide
  have hdescent : baseEnd_6489733 < baseStart_6489733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489763 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 4]
def baseStart_6489763 : Nat := 118140960795 + 6489763 * 2 ^ 59
def prefixEnd_6489763 : Nat := 4983230072969 + 3 ^ 40 * 6489763 * 2
def baseEnd_6489763 : Nat := 3332367752764597506116629

theorem tailTrace_6489763 : CollatzResearch.WordTrace tailWord_6489763 prefixEnd_6489763 3332367752764597506116629 := by
  unfold tailWord_6489763
  simp only [CollatzResearch.WordTrace]
  refine ⟨236701102387704489124201943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157800734925136326082801295 236701102387704489124201943)
  ·
    refine ⟨355051653581556733686302915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236701102387704489124201943 355051653581556733686302915)
    ·
      refine ⟨532577480372335100529454373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355051653581556733686302915 532577480372335100529454373)
      ·
        refine ⟨99858277569812831349272695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 532577480372335100529454373 99858277569812831349272695)
        ·
          refine ⟨149787416354719247023909043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99858277569812831349272695 149787416354719247023909043)
          ·
            refine ⟨224681124532078870535863565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149787416354719247023909043 224681124532078870535863565)
            ·
              refine ⟨84255421699529576450948837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224681124532078870535863565 84255421699529576450948837)
              ·
                refine ⟨15797891568661795584552907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84255421699529576450948837 15797891568661795584552907)
                ·
                  refine ⟨23696837352992693376829361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15797891568661795584552907 23696837352992693376829361)
                  ·
                    refine ⟨17772628014744520032622021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23696837352992693376829361 17772628014744520032622021)
                    ·
                      refine ⟨3332367752764597506116629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17772628014744520032622021 3332367752764597506116629)
                      ·
                        rfl

theorem cell23_6489763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_6489763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489763 prefixEnd_6489763 := by exact prefixLift 6489763
  have htrace : WordTrace (prefixWord ++ tailWord_6489763) baseStart_6489763 baseEnd_6489763 := by
    simpa [prefixWord, tailWord_6489763, baseEnd_6489763] using wordTrace_append hprefix tailTrace_6489763
  have hstable : (prefixWord ++ tailWord_6489763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489763).length < 2 ^ (prefixWord ++ tailWord_6489763).sum := by decide
  have hdescent : baseEnd_6489763 < baseStart_6489763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489773 : List Nat := [1, 5, 2, 1, 1, 1, 12]
def baseStart_6489773 : Nat := 118140960795 + 6489773 * 2 ^ 59
def prefixEnd_6489773 : Nat := 4983230072969 + 3 ^ 40 * 6489773 * 2
def baseEnd_6489773 : Nat := 41140406019396820580143

theorem tailTrace_6489773 : CollatzResearch.WordTrace tailWord_6489773 prefixEnd_6489773 41140406019396820580143 := by
  unfold tailWord_6489773
  simp only [CollatzResearch.WordTrace]
  refine ⟨236701467117668260832065973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157800978078445507221377315 236701467117668260832065973)
  ·
    refine ⟨22190762542281399453006185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 236701467117668260832065973 22190762542281399453006185)
    ·
      refine ⟨16643071906711049589754639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22190762542281399453006185 16643071906711049589754639)
      ·
        refine ⟨24964607860066574384631959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16643071906711049589754639 24964607860066574384631959)
        ·
          refine ⟨37446911790099861576947939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24964607860066574384631959 37446911790099861576947939)
          ·
            refine ⟨56170367685149792365421909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37446911790099861576947939 56170367685149792365421909)
            ·
              refine ⟨41140406019396820580143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 56170367685149792365421909 41140406019396820580143)
              ·
                rfl

theorem cell23_6489773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 12].length) (baseStart_6489773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489773 prefixEnd_6489773 := by exact prefixLift 6489773
  have htrace : WordTrace (prefixWord ++ tailWord_6489773) baseStart_6489773 baseEnd_6489773 := by
    simpa [prefixWord, tailWord_6489773, baseEnd_6489773] using wordTrace_append hprefix tailTrace_6489773
  have hstable : (prefixWord ++ tailWord_6489773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489773).length < 2 ^ (prefixWord ++ tailWord_6489773).sum := by decide
  have hdescent : baseEnd_6489773 < baseStart_6489773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489804 : List Nat := [2, 2, 1, 5, 2, 1, 2, 2, 1, 2, 3]
def baseStart_6489804 : Nat := 118140960795 + 6489804 * 2 ^ 59
def prefixEnd_6489804 : Nat := 4983230072969 + 3 ^ 40 * 6489804 * 2
def baseEnd_6489804 : Nat := 3332388805471431845703941

theorem tailTrace_6489804 : CollatzResearch.WordTrace tailWord_6489804 prefixEnd_6489804 3332388805471431845703941 := by
  unfold tailWord_6489804
  simp only [CollatzResearch.WordTrace]
  refine ⟨118351298890277976563222233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157801731853703968750962977 118351298890277976563222233)
  ·
    refine ⟨88763474167708482422416675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118351298890277976563222233 88763474167708482422416675)
    ·
      refine ⟨133145211251562723633625013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88763474167708482422416675 133145211251562723633625013)
      ·
        refine ⟨12482363554834005340652345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133145211251562723633625013 12482363554834005340652345)
        ·
          refine ⟨9361772666125504005489259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12482363554834005340652345 9361772666125504005489259)
          ·
            refine ⟨14042658999188256008233889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9361772666125504005489259 14042658999188256008233889)
            ·
              refine ⟨10531994249391192006175417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14042658999188256008233889 10531994249391192006175417)
              ·
                refine ⟨7898995687043394004631563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10531994249391192006175417 7898995687043394004631563)
                ·
                  refine ⟨11848493530565091006947345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7898995687043394004631563 11848493530565091006947345)
                  ·
                    refine ⟨8886370147923818255210509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11848493530565091006947345 8886370147923818255210509)
                    ·
                      refine ⟨3332388805471431845703941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8886370147923818255210509 3332388805471431845703941)
                      ·
                        rfl

theorem cell23_6489804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_6489804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489804 prefixEnd_6489804 := by exact prefixLift 6489804
  have htrace : WordTrace (prefixWord ++ tailWord_6489804) baseStart_6489804 baseEnd_6489804 := by
    simpa [prefixWord, tailWord_6489804, baseEnd_6489804] using wordTrace_append hprefix tailTrace_6489804
  have hstable : (prefixWord ++ tailWord_6489804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489804).length < 2 ^ (prefixWord ++ tailWord_6489804).sum := by decide
  have hdescent : baseEnd_6489804 < baseStart_6489804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489840 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 5, 4, 2]
def baseStart_6489840 : Nat := 118140960795 + 6489840 * 2 ^ 59
def prefixEnd_6489840 : Nat := 4983230072969 + 3 ^ 40 * 6489840 * 2
def baseEnd_6489840 : Nat := 3332407290774993704853775

theorem tailTrace_6489840 : CollatzResearch.WordTrace tailWord_6489840 prefixEnd_6489840 3332407290774993704853775 := by
  unfold tailWord_6489840
  simp only [CollatzResearch.WordTrace]
  refine ⟨118351955404212765637377487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157802607205617020849836649 118351955404212765637377487)
  ·
    refine ⟨177527933106319148456066231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118351955404212765637377487 177527933106319148456066231)
    ·
      refine ⟨266291899659478722684099347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177527933106319148456066231 266291899659478722684099347)
      ·
        refine ⟨399437849489218084026149021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266291899659478722684099347 399437849489218084026149021)
        ·
          refine ⟨149789193558456781509805883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399437849489218084026149021 149789193558456781509805883)
          ·
            refine ⟨224683790337685172264708825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149789193558456781509805883 224683790337685172264708825)
            ·
              refine ⟨168512842753263879198531619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224683790337685172264708825 168512842753263879198531619)
              ·
                refine ⟨252769264129895818797797429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168512842753263879198531619 252769264129895818797797429)
                ·
                  refine ⟨23697118512177733012293509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252769264129895818797797429 23697118512177733012293509)
                  ·
                    refine ⟨4443209721033324939805033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23697118512177733012293509 4443209721033324939805033)
                    ·
                      refine ⟨3332407290774993704853775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4443209721033324939805033 3332407290774993704853775)
                      ·
                        rfl

theorem cell23_6489840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5, 4, 2].length) (baseStart_6489840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489840 prefixEnd_6489840 := by exact prefixLift 6489840
  have htrace : WordTrace (prefixWord ++ tailWord_6489840) baseStart_6489840 baseEnd_6489840 := by
    simpa [prefixWord, tailWord_6489840, baseEnd_6489840] using wordTrace_append hprefix tailTrace_6489840
  have hstable : (prefixWord ++ tailWord_6489840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489840).length < 2 ^ (prefixWord ++ tailWord_6489840).sum := by decide
  have hdescent : baseEnd_6489840 < baseStart_6489840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489860 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 2, 1, 5]
def baseStart_6489860 : Nat := 118140960795 + 6489860 * 2 ^ 59
def prefixEnd_6489860 : Nat := 4983230072969 + 3 ^ 40 * 6489860 * 2
def baseEnd_6489860 : Nat := 3332417560388083626603683

theorem tailTrace_6489860 : CollatzResearch.WordTrace tailWord_6489860 prefixEnd_6489860 3332417560388083626603683 := by
  unfold tailWord_6489860
  simp only [CollatzResearch.WordTrace]
  refine ⟨118352320134176537345241517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157803093512235383126988689 118352320134176537345241517)
  ·
    refine ⟨44382120050316201504465569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118352320134176537345241517 44382120050316201504465569)
    ·
      refine ⟨33286590037737151128349177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44382120050316201504465569 33286590037737151128349177)
      ·
        refine ⟨24964942528302863346261883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33286590037737151128349177 24964942528302863346261883)
        ·
          refine ⟨37447413792454295019392825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24964942528302863346261883 37447413792454295019392825)
          ·
            refine ⟨28085560344340721264544619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37447413792454295019392825 28085560344340721264544619)
            ·
              refine ⟨42128340516511081896816929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28085560344340721264544619 42128340516511081896816929)
              ·
                refine ⟨31596255387383311422612697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42128340516511081896816929 31596255387383311422612697)
                ·
                  refine ⟨23697191540537483566959523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31596255387383311422612697 23697191540537483566959523)
                  ·
                    refine ⟨35545787310806225350439285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23697191540537483566959523 35545787310806225350439285)
                    ·
                      refine ⟨3332417560388083626603683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35545787310806225350439285 3332417560388083626603683)
                      ·
                        rfl

theorem cell23_6489860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_6489860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489860 prefixEnd_6489860 := by exact prefixLift 6489860
  have htrace : WordTrace (prefixWord ++ tailWord_6489860) baseStart_6489860 baseEnd_6489860 := by
    simpa [prefixWord, tailWord_6489860, baseEnd_6489860] using wordTrace_append hprefix tailTrace_6489860
  have hstable : (prefixWord ++ tailWord_6489860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489860).length < 2 ^ (prefixWord ++ tailWord_6489860).sum := by decide
  have hdescent : baseEnd_6489860 < baseStart_6489860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489874 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_6489874 : Nat := 118140960795 + 6489874 * 2 ^ 59
def prefixEnd_6489874 : Nat := 4983230072969 + 3 ^ 40 * 6489874 * 2
def baseEnd_6489874 : Nat := 3332424749117246571828619

theorem tailTrace_6489874 : CollatzResearch.WordTrace tailWord_6489874 prefixEnd_6489874 3332424749117246571828619 := by
  unfold tailWord_6489874
  simp only [CollatzResearch.WordTrace]
  refine ⟨59176287722575588770373169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157803433926868236720995117 59176287722575588770373169)
  ·
    refine ⟨44382215791931691577779877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59176287722575588770373169 44382215791931691577779877)
    ·
      refine ⟨8321665460987192170833727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44382215791931691577779877 8321665460987192170833727)
      ·
        refine ⟨12482498191480788256250591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8321665460987192170833727 12482498191480788256250591)
        ·
          refine ⟨18723747287221182384375887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12482498191480788256250591 18723747287221182384375887)
          ·
            refine ⟨28085620930831773576563831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18723747287221182384375887 28085620930831773576563831)
            ·
              refine ⟨42128431396247660364845747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28085620930831773576563831 42128431396247660364845747)
              ·
                refine ⟨63192647094371490547268621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42128431396247660364845747 63192647094371490547268621)
                ·
                  refine ⟨23697242660389308955225733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63192647094371490547268621 23697242660389308955225733)
                  ·
                    refine ⟨4443232998822995429104825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23697242660389308955225733 4443232998822995429104825)
                    ·
                      refine ⟨3332424749117246571828619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4443232998822995429104825 3332424749117246571828619)
                      ·
                        rfl

theorem cell23_6489874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_6489874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489874 prefixEnd_6489874 := by exact prefixLift 6489874
  have htrace : WordTrace (prefixWord ++ tailWord_6489874) baseStart_6489874 baseEnd_6489874 := by
    simpa [prefixWord, tailWord_6489874, baseEnd_6489874] using wordTrace_append hprefix tailTrace_6489874
  have hstable : (prefixWord ++ tailWord_6489874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489874).length < 2 ^ (prefixWord ++ tailWord_6489874).sum := by decide
  have hdescent : baseEnd_6489874 < baseStart_6489874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489907 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 3]
def baseStart_6489907 : Nat := 118140960795 + 6489907 * 2 ^ 59
def prefixEnd_6489907 : Nat := 4983230072969 + 3 ^ 40 * 6489907 * 2
def baseEnd_6489907 : Nat := 3332441693978844942715967

theorem tailTrace_6489907 : CollatzResearch.WordTrace tailWord_6489907 prefixEnd_6489907 3332441693978844942715967 := by
  unfold tailWord_6489907
  simp only [CollatzResearch.WordTrace]
  refine ⟨236706354499182801717443975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157804236332788534478295983 236706354499182801717443975)
  ·
    refine ⟨355059531748774202576165963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236706354499182801717443975 355059531748774202576165963)
    ·
      refine ⟨532589297623161303864248945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355059531748774202576165963 532589297623161303864248945)
      ·
        refine ⟨399441973217370977898186709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532589297623161303864248945 399441973217370977898186709)
        ·
          refine ⟨9361921247282132294488751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 399441973217370977898186709 9361921247282132294488751)
          ·
            refine ⟨14042881870923198441733127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9361921247282132294488751 14042881870923198441733127)
            ·
              refine ⟨21064322806384797662599691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14042881870923198441733127 21064322806384797662599691)
              ·
                refine ⟨31596484209577196493899537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21064322806384797662599691 31596484209577196493899537)
                ·
                  refine ⟨23697363157182897370424653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31596484209577196493899537 23697363157182897370424653)
                  ·
                    refine ⟨8886511183943586513909245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23697363157182897370424653 8886511183943586513909245)
                    ·
                      refine ⟨3332441693978844942715967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8886511183943586513909245 3332441693978844942715967)
                      ·
                        rfl

theorem cell23_6489907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 3, 3].length) (baseStart_6489907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489907 prefixEnd_6489907 := by exact prefixLift 6489907
  have htrace : WordTrace (prefixWord ++ tailWord_6489907) baseStart_6489907 baseEnd_6489907 := by
    simpa [prefixWord, tailWord_6489907, baseEnd_6489907] using wordTrace_append hprefix tailTrace_6489907
  have hstable : (prefixWord ++ tailWord_6489907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489907).length < 2 ^ (prefixWord ++ tailWord_6489907).sum := by decide
  have hdescent : baseEnd_6489907 < baseStart_6489907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489930 : List Nat := [3, 1, 2, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_6489930 : Nat := 118140960795 + 6489930 * 2 ^ 59
def prefixEnd_6489930 : Nat := 4983230072969 + 3 ^ 40 * 6489930 * 2
def baseEnd_6489930 : Nat := 3332453504033898352728361

theorem tailTrace_6489930 : CollatzResearch.WordTrace tailWord_6489930 prefixEnd_6489930 3332453504033898352728361 := by
  unfold tailWord_6489930
  simp only [CollatzResearch.WordTrace]
  refine ⟨59176798344524869161382811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157804795585399651097020829 59176798344524869161382811)
  ·
    refine ⟨88765197516787303742074217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59176798344524869161382811 88765197516787303742074217)
    ·
      refine ⟨66573898137590477806555663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88765197516787303742074217 66573898137590477806555663)
      ·
        refine ⟨99860847206385716709833495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66573898137590477806555663 99860847206385716709833495)
        ·
          refine ⟨149791270809578575064750243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99860847206385716709833495 149791270809578575064750243)
          ·
            refine ⟨224686906214367862597125365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149791270809578575064750243 224686906214367862597125365)
            ·
              refine ⟨21064397457596987118480503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 224686906214367862597125365 21064397457596987118480503)
              ·
                refine ⟨31596596186395480677720755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21064397457596987118480503 31596596186395480677720755)
                ·
                  refine ⟨47394894279593221016581133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31596596186395480677720755 47394894279593221016581133)
                  ·
                    refine ⟨17773085354847457881217925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47394894279593221016581133 17773085354847457881217925)
                    ·
                      refine ⟨3332453504033898352728361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17773085354847457881217925 3332453504033898352728361)
                      ·
                        rfl

theorem cell23_6489930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_6489930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489930 prefixEnd_6489930 := by exact prefixLift 6489930
  have htrace : WordTrace (prefixWord ++ tailWord_6489930) baseStart_6489930 baseEnd_6489930 := by
    simpa [prefixWord, tailWord_6489930, baseEnd_6489930] using wordTrace_append hprefix tailTrace_6489930
  have hstable : (prefixWord ++ tailWord_6489930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489930).length < 2 ^ (prefixWord ++ tailWord_6489930).sum := by decide
  have hdescent : baseEnd_6489930 < baseStart_6489930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6489960 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 2, 1, 6]
def baseStart_6489960 : Nat := 118140960795 + 6489960 * 2 ^ 59
def prefixEnd_6489960 : Nat := 4983230072969 + 3 ^ 40 * 6489960 * 2
def baseEnd_6489960 : Nat := 3332468908453533235353223

theorem tailTrace_6489960 : CollatzResearch.WordTrace tailWord_6489960 prefixEnd_6489960 3332468908453533235353223 := by
  unfold tailWord_6489960
  simp only [CollatzResearch.WordTrace]
  refine ⟨118354143783995395884561667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157805525045327194512748889 118354143783995395884561667)
  ·
    refine ⟨177531215675993093826842501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118354143783995395884561667 177531215675993093826842501)
    ·
      refine ⟨33287102939248705092532969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177531215675993093826842501 33287102939248705092532969)
      ·
        refine ⟨24965327204436528819399727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33287102939248705092532969 24965327204436528819399727)
        ·
          refine ⟨37447990806654793229099591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24965327204436528819399727 37447990806654793229099591)
          ·
            refine ⟨56171986209982189843649387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37447990806654793229099591 56171986209982189843649387)
            ·
              refine ⟨84257979314973284765474081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56171986209982189843649387 84257979314973284765474081)
              ·
                refine ⟨63193484486229963574105561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84257979314973284765474081 63193484486229963574105561)
                ·
                  refine ⟨47395113364672472680579171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63193484486229963574105561 47395113364672472680579171)
                  ·
                    refine ⟨71092670047008709020868757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47395113364672472680579171 71092670047008709020868757)
                    ·
                      refine ⟨3332468908453533235353223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71092670047008709020868757 3332468908453533235353223)
                      ·
                        rfl

theorem cell23_6489960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_6489960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6489960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6489960 prefixEnd_6489960 := by exact prefixLift 6489960
  have htrace : WordTrace (prefixWord ++ tailWord_6489960) baseStart_6489960 baseEnd_6489960 := by
    simpa [prefixWord, tailWord_6489960, baseEnd_6489960] using wordTrace_append hprefix tailTrace_6489960
  have hstable : (prefixWord ++ tailWord_6489960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6489960).length < 2 ^ (prefixWord ++ tailWord_6489960).sum := by decide
  have hdescent : baseEnd_6489960 < baseStart_6489960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6489960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490008 : List Nat := [2, 1, 2, 6, 2, 1, 1, 1, 3, 4]
def baseStart_6490008 : Nat := 118140960795 + 6490008 * 2 ^ 59
def prefixEnd_6490008 : Nat := 4983230072969 + 3 ^ 40 * 6490008 * 2
def baseEnd_6490008 : Nat := 1110831185174983015851001

theorem tailTrace_6490008 : CollatzResearch.WordTrace tailWord_6490008 prefixEnd_6490008 1110831185174983015851001 := by
  unfold tailWord_6490008
  simp only [CollatzResearch.WordTrace]
  refine ⟨118355019135908447983435339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157806692181211263977913785 118355019135908447983435339)
  ·
    refine ⟨177532528703862671975153009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118355019135908447983435339 177532528703862671975153009)
    ·
      refine ⟨133149396527897003981364757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177532528703862671975153009 133149396527897003981364757)
      ·
        refine ⟨6241377962245172061626473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133149396527897003981364757 6241377962245172061626473)
        ·
          refine ⟨4681033471683879046219855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6241377962245172061626473 4681033471683879046219855)
          ·
            refine ⟨7021550207525818569329783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4681033471683879046219855 7021550207525818569329783)
            ·
              refine ⟨10532325311288727853994675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7021550207525818569329783 10532325311288727853994675)
              ·
                refine ⟨15798487966933091780992013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10532325311288727853994675 15798487966933091780992013)
                ·
                  refine ⟨5924432987599909417872005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15798487966933091780992013 5924432987599909417872005)
                  ·
                    refine ⟨1110831185174983015851001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5924432987599909417872005 1110831185174983015851001)
                    ·
                      rfl

theorem cell23_6490008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_6490008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490008 prefixEnd_6490008 := by exact prefixLift 6490008
  have htrace : WordTrace (prefixWord ++ tailWord_6490008) baseStart_6490008 baseEnd_6490008 := by
    simpa [prefixWord, tailWord_6490008, baseEnd_6490008] using wordTrace_append hprefix tailTrace_6490008
  have hstable : (prefixWord ++ tailWord_6490008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490008).length < 2 ^ (prefixWord ++ tailWord_6490008).sum := by decide
  have hdescent : baseEnd_6490008 < baseStart_6490008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490060 : List Nat := [2, 2, 1, 4, 1, 13]
def baseStart_6490060 : Nat := 118140960795 + 6490060 * 2 ^ 59
def prefixEnd_6490060 : Nat := 4983230072969 + 3 ^ 40 * 6490060 * 2
def baseEnd_6490060 : Nat := 13714075129707748329641

theorem tailTrace_6490060 : CollatzResearch.WordTrace tailWord_6490060 prefixEnd_6490060 13714075129707748329641 := by
  unfold tailWord_6490060
  simp only [CollatzResearch.WordTrace]
  refine ⟨118355967433814254423881817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157807956578419005898509089 118355967433814254423881817)
  ·
    refine ⟨88766975575360690817911363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118355967433814254423881817 88766975575360690817911363)
    ·
      refine ⟨133150463363041036226867045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88766975575360690817911363 133150463363041036226867045)
      ·
        refine ⟨24965711880570194292537571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133150463363041036226867045 24965711880570194292537571)
        ·
          refine ⟨37448567820855291438806357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24965711880570194292537571 37448567820855291438806357)
          ·
            refine ⟨13714075129707748329641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 37448567820855291438806357 13714075129707748329641)
            ·
              rfl

theorem cell23_6490060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 13].length) (baseStart_6490060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490060 prefixEnd_6490060 := by exact prefixLift 6490060
  have htrace : WordTrace (prefixWord ++ tailWord_6490060) baseStart_6490060 baseEnd_6490060 := by
    simpa [prefixWord, tailWord_6490060, baseEnd_6490060] using wordTrace_append hprefix tailTrace_6490060
  have hstable : (prefixWord ++ tailWord_6490060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490060).length < 2 ^ (prefixWord ++ tailWord_6490060).sum := by decide
  have hdescent : baseEnd_6490060 < baseStart_6490060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490080 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 6]
def baseStart_6490080 : Nat := 118140960795 + 6490080 * 2 ^ 59
def prefixEnd_6490080 : Nat := 4983230072969 + 3 ^ 40 * 6490080 * 2
def baseEnd_6490080 : Nat := 3332530526132072765852671

theorem tailTrace_6490080 : CollatzResearch.WordTrace tailWord_6490080 prefixEnd_6490080 3332530526132072765852671 := by
  unfold tailWord_6490080
  simp only [CollatzResearch.WordTrace]
  refine ⟨118356332163778026131745847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157808442885037368175661129 118356332163778026131745847)
  ·
    refine ⟨177534498245667039197618771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118356332163778026131745847 177534498245667039197618771)
    ·
      refine ⟨266301747368500558796428157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177534498245667039197618771 266301747368500558796428157)
      ·
        refine ⟨99863155263187709548660559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266301747368500558796428157 99863155263187709548660559)
        ·
          refine ⟨149794732894781564322990839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99863155263187709548660559 149794732894781564322990839)
          ·
            refine ⟨224692099342172346484486259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149794732894781564322990839 224692099342172346484486259)
            ·
              refine ⟨337038149013258519726729389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224692099342172346484486259 337038149013258519726729389)
              ·
                refine ⟨126389305879971944897523521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 337038149013258519726729389 126389305879971944897523521)
                ·
                  refine ⟨94791979409978958673142641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126389305879971944897523521 94791979409978958673142641)
                  ·
                    refine ⟨71093984557484219004856981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94791979409978958673142641 71093984557484219004856981)
                    ·
                      refine ⟨3332530526132072765852671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71093984557484219004856981 3332530526132072765852671)
                      ·
                        rfl

theorem cell23_6490080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_6490080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490080 prefixEnd_6490080 := by exact prefixLift 6490080
  have htrace : WordTrace (prefixWord ++ tailWord_6490080) baseStart_6490080 baseEnd_6490080 := by
    simpa [prefixWord, tailWord_6490080, baseEnd_6490080] using wordTrace_append hprefix tailTrace_6490080
  have hstable : (prefixWord ++ tailWord_6490080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490080).length < 2 ^ (prefixWord ++ tailWord_6490080).sum := by decide
  have hdescent : baseEnd_6490080 < baseStart_6490080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490094 : List Nat := [4, 1, 2, 1, 3, 2, 3, 7]
def baseStart_6490094 : Nat := 118140960795 + 6490094 * 2 ^ 59
def prefixEnd_6490094 : Nat := 4983230072969 + 3 ^ 40 * 6490094 * 2
def baseEnd_6490094 : Nat := 123427322772638359669541

theorem tailTrace_6490094 : CollatzResearch.WordTrace tailWord_6490094 prefixEnd_6490094 123427322772638359669541 := by
  unfold tailWord_6490094
  simp only [CollatzResearch.WordTrace]
  refine ⟨29589146868688166581812667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157808783299670221769667557 29589146868688166581812667)
  ·
    refine ⟨44383720303032249872719001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29589146868688166581812667 44383720303032249872719001)
    ·
      refine ⟨33287790227274187404539251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44383720303032249872719001 33287790227274187404539251)
      ·
        refine ⟨49931685340911281106808877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33287790227274187404539251 49931685340911281106808877)
        ·
          refine ⟨18724382002841730415053329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49931685340911281106808877 18724382002841730415053329)
          ·
            refine ⟨14043286502131297811289997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18724382002841730415053329 14043286502131297811289997)
            ·
              refine ⟨5266232438299236679233749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14043286502131297811289997 5266232438299236679233749)
              ·
                refine ⟨123427322772638359669541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5266232438299236679233749 123427322772638359669541)
                ·
                  rfl

theorem cell23_6490094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 3, 7].length) (baseStart_6490094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490094 prefixEnd_6490094 := by exact prefixLift 6490094
  have htrace : WordTrace (prefixWord ++ tailWord_6490094) baseStart_6490094 baseEnd_6490094 := by
    simpa [prefixWord, tailWord_6490094, baseEnd_6490094] using wordTrace_append hprefix tailTrace_6490094
  have hstable : (prefixWord ++ tailWord_6490094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490094).length < 2 ^ (prefixWord ++ tailWord_6490094).sum := by decide
  have hdescent : baseEnd_6490094 < baseStart_6490094 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490138 : List Nat := [3, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3]
def baseStart_6490138 : Nat := 118140960795 + 6490138 * 2 ^ 59
def prefixEnd_6490138 : Nat := 4983230072969 + 3 ^ 40 * 6490138 * 2
def baseEnd_6490138 : Nat := 3332560308010033538927405

theorem tailTrace_6490138 : CollatzResearch.WordTrace tailWord_6490138 prefixEnd_6490138 3332560308010033538927405 := by
  unfold tailWord_6490138
  simp only [CollatzResearch.WordTrace]
  refine ⟨59178694940336482042275767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157809853174230618779402045 59178694940336482042275767)
  ·
    refine ⟨88768042410504723063413651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59178694940336482042275767 88768042410504723063413651)
    ·
      refine ⟨133152063615757084595120477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88768042410504723063413651 133152063615757084595120477)
      ·
        refine ⟨49932023855908906723170179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133152063615757084595120477 49932023855908906723170179)
        ·
          refine ⟨74898035783863360084755269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49932023855908906723170179 74898035783863360084755269)
          ·
            refine ⟨14043381709474380015891613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74898035783863360084755269 14043381709474380015891613)
            ·
              refine ⟨5266268141052892505959355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14043381709474380015891613 5266268141052892505959355)
              ·
                refine ⟨7899402211579338758939033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5266268141052892505959355 7899402211579338758939033)
                ·
                  refine ⟨5924551658684504069204275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7899402211579338758939033 5924551658684504069204275)
                  ·
                    refine ⟨8886827488026756103806413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5924551658684504069204275 8886827488026756103806413)
                    ·
                      refine ⟨3332560308010033538927405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8886827488026756103806413 3332560308010033538927405)
                      ·
                        rfl

theorem cell23_6490138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_6490138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490138 prefixEnd_6490138 := by exact prefixLift 6490138
  have htrace : WordTrace (prefixWord ++ tailWord_6490138) baseStart_6490138 baseEnd_6490138 := by
    simpa [prefixWord, tailWord_6490138, baseEnd_6490138] using wordTrace_append hprefix tailTrace_6490138
  have hstable : (prefixWord ++ tailWord_6490138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490138).length < 2 ^ (prefixWord ++ tailWord_6490138).sum := by decide
  have hdescent : baseEnd_6490138 < baseStart_6490138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490147 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 5]
def baseStart_6490147 : Nat := 118140960795 + 6490147 * 2 ^ 59
def prefixEnd_6490147 : Nat := 4983230072969 + 3 ^ 40 * 6490147 * 2
def baseEnd_6490147 : Nat := 3332564929335924003714863

theorem tailTrace_6490147 : CollatzResearch.WordTrace tailWord_6490147 prefixEnd_6490147 3332564929335924003714863 := by
  unfold tailWord_6490147
  simp only [CollatzResearch.WordTrace]
  refine ⟨236715108018313322706180695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157810072012208881804120463 236715108018313322706180695)
  ·
    refine ⟨355072662027469984059271043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236715108018313322706180695 355072662027469984059271043)
    ·
      refine ⟨532608993041204976088906565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355072662027469984059271043 532608993041204976088906565)
      ·
        refine ⟨99864186195225933016669981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 532608993041204976088906565 99864186195225933016669981)
        ·
          refine ⟨37449069823209724881251243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99864186195225933016669981 37449069823209724881251243)
          ·
            refine ⟨56173604734814587321876865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37449069823209724881251243 56173604734814587321876865)
            ·
              refine ⟨42130203551110940491407649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56173604734814587321876865 42130203551110940491407649)
              ·
                refine ⟨31597652663333205368555737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42130203551110940491407649 31597652663333205368555737)
                ·
                  refine ⟨23698239497499904026416803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31597652663333205368555737 23698239497499904026416803)
                  ·
                    refine ⟨35547359246249856039625205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23698239497499904026416803 35547359246249856039625205)
                    ·
                      refine ⟨3332564929335924003714863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35547359246249856039625205 3332564929335924003714863)
                      ·
                        rfl

theorem cell23_6490147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_6490147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490147 prefixEnd_6490147 := by exact prefixLift 6490147
  have htrace : WordTrace (prefixWord ++ tailWord_6490147) baseStart_6490147 baseEnd_6490147 := by
    simpa [prefixWord, tailWord_6490147, baseEnd_6490147] using wordTrace_append hprefix tailTrace_6490147
  have hstable : (prefixWord ++ tailWord_6490147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490147).length < 2 ^ (prefixWord ++ tailWord_6490147).sum := by decide
  have hdescent : baseEnd_6490147 < baseStart_6490147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490161 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 4, 2, 2]
def baseStart_6490161 : Nat := 118140960795 + 6490161 * 2 ^ 59
def prefixEnd_6490161 : Nat := 4983230072969 + 3 ^ 40 * 6490161 * 2
def baseEnd_6490161 : Nat := 3332572118065086948939799

theorem tailTrace_6490161 : CollatzResearch.WordTrace tailWord_6490161 prefixEnd_6490161 3332572118065086948939799 := by
  unfold tailWord_6490161
  simp only [CollatzResearch.WordTrace]
  refine ⟨236715618640262603097190337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157810412426841735398126891 236715618640262603097190337)
  ·
    refine ⟨177536713980196952322892753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236715618640262603097190337 177536713980196952322892753)
    ·
      refine ⟨133152535485147714242169565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177536713980196952322892753 133152535485147714242169565)
      ·
        refine ⟨49932200806930392840813587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133152535485147714242169565 49932200806930392840813587)
        ·
          refine ⟨74898301210395589261220381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49932200806930392840813587 74898301210395589261220381)
          ·
            refine ⟨28086862953898345972957643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74898301210395589261220381 28086862953898345972957643)
            ·
              refine ⟨42130294430847518959436465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28086862953898345972957643 42130294430847518959436465)
              ·
                refine ⟨31597720823135639219577349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42130294430847518959436465 31597720823135639219577349)
                ·
                  refine ⟨5924572654337932353670753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31597720823135639219577349 5924572654337932353670753)
                  ·
                    refine ⟨4443429490753449265253065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5924572654337932353670753 4443429490753449265253065)
                    ·
                      refine ⟨3332572118065086948939799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4443429490753449265253065 3332572118065086948939799)
                      ·
                        rfl

theorem cell23_6490161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_6490161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490161 prefixEnd_6490161 := by exact prefixLift 6490161
  have htrace : WordTrace (prefixWord ++ tailWord_6490161) baseStart_6490161 baseEnd_6490161 := by
    simpa [prefixWord, tailWord_6490161, baseEnd_6490161] using wordTrace_append hprefix tailTrace_6490161
  have hstable : (prefixWord ++ tailWord_6490161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490161).length < 2 ^ (prefixWord ++ tailWord_6490161).sum := by decide
  have hdescent : baseEnd_6490161 < baseStart_6490161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490234 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2]
def baseStart_6490234 : Nat := 118140960795 + 6490234 * 2 ^ 59
def prefixEnd_6490234 : Nat := 4983230072969 + 3 ^ 40 * 6490234 * 2
def baseEnd_6490234 : Nat := 3332609602152865163326963

theorem tailTrace_6490234 : CollatzResearch.WordTrace tailWord_6490234 prefixEnd_6490234 3332609602152865163326963 := by
  unfold tailWord_6490234
  simp only [CollatzResearch.WordTrace]
  refine ⟨59179570292249534141149439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157812187445998757709731837 59179570292249534141149439)
  ·
    refine ⟨88769355438374301211724159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59179570292249534141149439 88769355438374301211724159)
    ·
      refine ⟨133154033157561451817586239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88769355438374301211724159 133154033157561451817586239)
      ·
        refine ⟨199731049736342177726379359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133154033157561451817586239 199731049736342177726379359)
        ·
          refine ⟨299596574604513266589569039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199731049736342177726379359 299596574604513266589569039)
          ·
            refine ⟨449394861906769899884353559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299596574604513266589569039 449394861906769899884353559)
            ·
              refine ⟨674092292860154849826530339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449394861906769899884353559 674092292860154849826530339)
              ·
                refine ⟨1011138439290232274739795509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674092292860154849826530339 1011138439290232274739795509)
                ·
                  refine ⟨94794228683459275756855829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1011138439290232274739795509 94794228683459275756855829)
                  ·
                    refine ⟨4443479469537153551102617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94794228683459275756855829 4443479469537153551102617)
                    ·
                      refine ⟨3332609602152865163326963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4443479469537153551102617 3332609602152865163326963)
                      ·
                        rfl

theorem cell23_6490234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2].length) (baseStart_6490234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490234 prefixEnd_6490234 := by exact prefixLift 6490234
  have htrace : WordTrace (prefixWord ++ tailWord_6490234) baseStart_6490234 baseEnd_6490234 := by
    simpa [prefixWord, tailWord_6490234, baseEnd_6490234] using wordTrace_append hprefix tailTrace_6490234
  have hstable : (prefixWord ++ tailWord_6490234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490234).length < 2 ^ (prefixWord ++ tailWord_6490234).sum := by decide
  have hdescent : baseEnd_6490234 < baseStart_6490234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490271 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 3]
def baseStart_6490271 : Nat := 118140960795 + 6490271 * 2 ^ 59
def prefixEnd_6490271 : Nat := 4983230072969 + 3 ^ 40 * 6490271 * 2
def baseEnd_6490271 : Nat := 3332628600937081518564293

theorem tailTrace_6490271 : CollatzResearch.WordTrace tailWord_6490271 prefixEnd_6490271 3332628600937081518564293 := by
  unfold tailWord_6490271
  simp only [CollatzResearch.WordTrace]
  refine ⟨236719630669864091883694667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157813087113242727922463111 236719630669864091883694667)
  ·
    refine ⟨355079446004796137825542001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236719630669864091883694667 355079446004796137825542001)
    ·
      refine ⟨266309584503597103369156501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355079446004796137825542001 266309584503597103369156501)
      ·
        refine ⟨12483261773606114220429211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 266309584503597103369156501 12483261773606114220429211)
        ·
          refine ⟨18724892660409171330643817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12483261773606114220429211 18724892660409171330643817)
          ·
            refine ⟨14043669495306878497982863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18724892660409171330643817 14043669495306878497982863)
            ·
              refine ⟨21065504242960317746974295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14043669495306878497982863 21065504242960317746974295)
              ·
                refine ⟨31598256364440476620461443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21065504242960317746974295 31598256364440476620461443)
                ·
                  refine ⟨47397384546660714930692165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31598256364440476620461443 47397384546660714930692165)
                  ·
                    refine ⟨8887009602498884049504781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47397384546660714930692165 8887009602498884049504781)
                    ·
                      refine ⟨3332628600937081518564293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8887009602498884049504781 3332628600937081518564293)
                      ·
                        rfl

theorem cell23_6490271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_6490271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490271 prefixEnd_6490271 := by exact prefixLift 6490271
  have htrace : WordTrace (prefixWord ++ tailWord_6490271) baseStart_6490271 baseEnd_6490271 := by
    simpa [prefixWord, tailWord_6490271, baseEnd_6490271] using wordTrace_append hprefix tailTrace_6490271
  have hstable : (prefixWord ++ tailWord_6490271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490271).length < 2 ^ (prefixWord ++ tailWord_6490271).sum := by decide
  have hdescent : baseEnd_6490271 < baseStart_6490271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490308 : List Nat := [2, 3, 3, 1, 2, 2, 3, 1, 6]
def baseStart_6490308 : Nat := 118140960795 + 6490308 * 2 ^ 59
def prefixEnd_6490308 : Nat := 4983230072969 + 3 ^ 40 * 6490308 * 2
def baseEnd_6490308 : Nat := 370294177746810874866847

theorem tailTrace_6490308 : CollatzResearch.WordTrace tailWord_6490308 prefixEnd_6490308 370294177746810874866847 := by
  unfold tailWord_6490308
  simp only [CollatzResearch.WordTrace]
  refine ⟨118360490085365023601395789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157813986780486698135194385 118360490085365023601395789)
  ·
    refine ⟨44385183782011883850523421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118360490085365023601395789 44385183782011883850523421)
    ·
      refine ⟨16644443918254456443946283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44385183782011883850523421 16644443918254456443946283)
      ·
        refine ⟨24966665877381684665919425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16644443918254456443946283 24966665877381684665919425)
        ·
          refine ⟨18724999408036263499439569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24966665877381684665919425 18724999408036263499439569)
          ·
            refine ⟨14043749556027197624579677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18724999408036263499439569 14043749556027197624579677)
            ·
              refine ⟨5266406083510199109217379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14043749556027197624579677 5266406083510199109217379)
              ·
                refine ⟨7899609125265298663826069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5266406083510199109217379 7899609125265298663826069)
                ·
                  refine ⟨370294177746810874866847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7899609125265298663826069 370294177746810874866847)
                  ·
                    rfl

theorem cell23_6490308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_6490308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490308 prefixEnd_6490308 := by exact prefixLift 6490308
  have htrace : WordTrace (prefixWord ++ tailWord_6490308) baseStart_6490308 baseEnd_6490308 := by
    simpa [prefixWord, tailWord_6490308, baseEnd_6490308] using wordTrace_append hprefix tailTrace_6490308
  have hstable : (prefixWord ++ tailWord_6490308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490308).length < 2 ^ (prefixWord ++ tailWord_6490308).sum := by decide
  have hdescent : baseEnd_6490308 < baseStart_6490308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490318 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3]
def baseStart_6490318 : Nat := 118140960795 + 6490318 * 2 ^ 59
def prefixEnd_6490318 : Nat := 4983230072969 + 3 ^ 40 * 6490318 * 2
def baseEnd_6490318 : Nat := 3332652734527842834676577

theorem tailTrace_6490318 : CollatzResearch.WordTrace tailWord_6490318 prefixEnd_6490318 3332652734527842834676577 := by
  unfold tailWord_6490318
  simp only [CollatzResearch.WordTrace]
  refine ⟨29590168112586727363831951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157814229933795879273770405 29590168112586727363831951)
  ·
    refine ⟨44385252168880091045747927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29590168112586727363831951 44385252168880091045747927)
    ·
      refine ⟨66577878253320136568621891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44385252168880091045747927 66577878253320136568621891)
      ·
        refine ⟨99866817379980204852932837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66577878253320136568621891 99866817379980204852932837)
        ·
          refine ⟨18725028258746288409924907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99866817379980204852932837 18725028258746288409924907)
          ·
            refine ⟨28087542388119432614887361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18725028258746288409924907 28087542388119432614887361)
            ·
              refine ⟨21065656791089574461165521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28087542388119432614887361 21065656791089574461165521)
              ·
                refine ⟨15799242593317180845874141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21065656791089574461165521 15799242593317180845874141)
                ·
                  refine ⟨5924715972493942817202803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15799242593317180845874141 5924715972493942817202803)
                  ·
                    refine ⟨8887073958740914225804205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5924715972493942817202803 8887073958740914225804205)
                    ·
                      refine ⟨3332652734527842834676577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8887073958740914225804205 3332652734527842834676577)
                      ·
                        rfl

theorem cell23_6490318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_6490318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490318 prefixEnd_6490318 := by exact prefixLift 6490318
  have htrace : WordTrace (prefixWord ++ tailWord_6490318) baseStart_6490318 baseEnd_6490318 := by
    simpa [prefixWord, tailWord_6490318, baseEnd_6490318] using wordTrace_append hprefix tailTrace_6490318
  have hstable : (prefixWord ++ tailWord_6490318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490318).length < 2 ^ (prefixWord ++ tailWord_6490318).sum := by decide
  have hdescent : baseEnd_6490318 < baseStart_6490318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490351 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 4, 4]
def baseStart_6490351 : Nat := 118140960795 + 6490351 * 2 ^ 59
def prefixEnd_6490351 : Nat := 4983230072969 + 3 ^ 40 * 6490351 * 2
def baseEnd_6490351 : Nat := 1110889893129813735187975

theorem tailTrace_6490351 : CollatzResearch.WordTrace tailWord_6490351 prefixEnd_6490351 1110889893129813735187975 := by
  unfold tailWord_6490351
  simp only [CollatzResearch.WordTrace]
  refine ⟨236722548509574265546606907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157815032339716177031071271 236722548509574265546606907)
  ·
    refine ⟨355083822764361398319910361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236722548509574265546606907 355083822764361398319910361)
    ·
      refine ⟨266312867073271048739932771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355083822764361398319910361 266312867073271048739932771)
      ·
        refine ⟨399469300609906573109899157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266312867073271048739932771 399469300609906573109899157)
        ·
          refine ⟨18725123466089370614526523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 399469300609906573109899157 18725123466089370614526523)
          ·
            refine ⟨28087685199134055921789785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18725123466089370614526523 28087685199134055921789785)
            ·
              refine ⟨21065763899350541941342339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28087685199134055921789785 21065763899350541941342339)
              ·
                refine ⟨31598645849025812912013509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21065763899350541941342339 31598645849025812912013509)
                ·
                  refine ⟨5924746096692339921002533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31598645849025812912013509 5924746096692339921002533)
                  ·
                    refine ⟨1110889893129813735187975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5924746096692339921002533 1110889893129813735187975)
                    ·
                      rfl

theorem cell23_6490351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 4, 4].length) (baseStart_6490351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490351 prefixEnd_6490351 := by exact prefixLift 6490351
  have htrace : WordTrace (prefixWord ++ tailWord_6490351) baseStart_6490351 baseEnd_6490351 := by
    simpa [prefixWord, tailWord_6490351, baseEnd_6490351] using wordTrace_append hprefix tailTrace_6490351
  have hstable : (prefixWord ++ tailWord_6490351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490351).length < 2 ^ (prefixWord ++ tailWord_6490351).sum := by decide
  have hdescent : baseEnd_6490351 < baseStart_6490351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490364 : List Nat := [2, 2, 2, 1, 4, 1, 1, 10]
def baseStart_6490364 : Nat := 118140960795 + 6490364 * 2 ^ 59
def prefixEnd_6490364 : Nat := 4983230072969 + 3 ^ 40 * 6490364 * 2
def baseEnd_6490364 : Nat := 123432457579183320544495

theorem tailTrace_6490364 : CollatzResearch.WordTrace tailWord_6490364 prefixEnd_6490364 123432457579183320544495 := by
  unfold tailWord_6490364
  simp only [CollatzResearch.WordTrace]
  refine ⟨118361511329263584383415073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157815348439018112511220097 118361511329263584383415073)
  ·
    refine ⟨88771133496947688287561305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118361511329263584383415073 88771133496947688287561305)
    ·
      refine ⟨66578350122710766215670979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88771133496947688287561305 66578350122710766215670979)
      ·
        refine ⟨99867525184066149323506469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66578350122710766215670979 99867525184066149323506469)
        ·
          refine ⟨18725160972012402998157463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99867525184066149323506469 18725160972012402998157463)
          ·
            refine ⟨28087741458018604497236195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18725160972012402998157463 28087741458018604497236195)
            ·
              refine ⟨42131612187027906745854293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28087741458018604497236195 42131612187027906745854293)
              ·
                refine ⟨123432457579183320544495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42131612187027906745854293 123432457579183320544495)
                ·
                  rfl

theorem cell23_6490364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 10].length) (baseStart_6490364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490364 prefixEnd_6490364 := by exact prefixLift 6490364
  have htrace : WordTrace (prefixWord ++ tailWord_6490364) baseStart_6490364 baseEnd_6490364 := by
    simpa [prefixWord, tailWord_6490364, baseEnd_6490364] using wordTrace_append hprefix tailTrace_6490364
  have hstable : (prefixWord ++ tailWord_6490364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490364).length < 2 ^ (prefixWord ++ tailWord_6490364).sum := by decide
  have hdescent : baseEnd_6490364 < baseStart_6490364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490368 : List Nat := [2, 1, 1, 2, 1, 1, 8, 1, 2, 4]
def baseStart_6490368 : Nat := 118140960795 + 6490368 * 2 ^ 59
def prefixEnd_6490368 : Nat := 4983230072969 + 3 ^ 40 * 6490368 * 2
def baseEnd_6490368 : Nat := 1110892802853522546350449

theorem tailTrace_6490368 : CollatzResearch.WordTrace tailWord_6490368 prefixEnd_6490368 1110892802853522546350449 := by
  unfold tailWord_6490368
  simp only [CollatzResearch.WordTrace]
  refine ⟨118361584275256338724987879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157815445700341784966650505 118361584275256338724987879)
  ·
    refine ⟨177542376412884508087481819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118361584275256338724987879 177542376412884508087481819)
    ·
      refine ⟨266313564619326762131222729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177542376412884508087481819 266313564619326762131222729)
      ·
        refine ⟨199735173464495071598417047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266313564619326762131222729 199735173464495071598417047)
        ·
          refine ⟨299602760196742607397625571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199735173464495071598417047 299602760196742607397625571)
          ·
            refine ⟨449404140295113911096438357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299602760196742607397625571 449404140295113911096438357)
            ·
              refine ⟨5266454769083366145661387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 449404140295113911096438357 5266454769083366145661387)
              ·
                refine ⟨7899682153625049218492081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5266454769083366145661387 7899682153625049218492081)
                ·
                  refine ⟨5924761615218786913869061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7899682153625049218492081 5924761615218786913869061)
                  ·
                    refine ⟨1110892802853522546350449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5924761615218786913869061 1110892802853522546350449)
                    ·
                      rfl

theorem cell23_6490368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 2, 4].length) (baseStart_6490368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490368 prefixEnd_6490368 := by exact prefixLift 6490368
  have htrace : WordTrace (prefixWord ++ tailWord_6490368) baseStart_6490368 baseEnd_6490368 := by
    simpa [prefixWord, tailWord_6490368, baseEnd_6490368] using wordTrace_append hprefix tailTrace_6490368
  have hstable : (prefixWord ++ tailWord_6490368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490368).length < 2 ^ (prefixWord ++ tailWord_6490368).sum := by decide
  have hdescent : baseEnd_6490368 < baseStart_6490368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490378 : List Nat := [3, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3]
def baseStart_6490378 : Nat := 118140960795 + 6490378 * 2 ^ 59
def prefixEnd_6490378 : Nat := 4983230072969 + 3 ^ 40 * 6490378 * 2
def baseEnd_6490378 : Nat := 3332683543367112599926301

theorem tailTrace_6490378 : CollatzResearch.WordTrace tailWord_6490378 prefixEnd_6490378 3332683543367112599926301 := by
  unfold tailWord_6490378
  simp only [CollatzResearch.WordTrace]
  refine ⟨59180883320119112289459947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157815688853650966105226525 59180883320119112289459947)
  ·
    refine ⟨88771324980178668434189921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59180883320119112289459947 88771324980178668434189921)
    ·
      refine ⟨66578493735134001325642441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88771324980178668434189921 66578493735134001325642441)
      ·
        refine ⟨49933870301350500994231831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66578493735134001325642441 49933870301350500994231831)
        ·
          refine ⟨74900805452025751491347747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49933870301350500994231831 74900805452025751491347747)
          ·
            refine ⟨112351208178038627237021621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74900805452025751491347747 112351208178038627237021621)
            ·
              refine ⟨10532925766691121303470777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112351208178038627237021621 10532925766691121303470777)
              ·
                refine ⟨7899694325018340977603083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10532925766691121303470777 7899694325018340977603083)
                ·
                  refine ⟨11849541487527511466404625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7899694325018340977603083 11849541487527511466404625)
                  ·
                    refine ⟨8887156115645633599803469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11849541487527511466404625 8887156115645633599803469)
                    ·
                      refine ⟨3332683543367112599926301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8887156115645633599803469 3332683543367112599926301)
                      ·
                        rfl

theorem cell23_6490378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_6490378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490378 prefixEnd_6490378 := by exact prefixLift 6490378
  have htrace : WordTrace (prefixWord ++ tailWord_6490378) baseStart_6490378 baseEnd_6490378 := by
    simpa [prefixWord, tailWord_6490378, baseEnd_6490378] using wordTrace_append hprefix tailTrace_6490378
  have hstable : (prefixWord ++ tailWord_6490378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490378).length < 2 ^ (prefixWord ++ tailWord_6490378).sum := by decide
  have hdescent : baseEnd_6490378 < baseStart_6490378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490391 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 3]
def baseStart_6490391 : Nat := 118140960795 + 6490391 * 2 ^ 59
def prefixEnd_6490391 : Nat := 4983230072969 + 3 ^ 40 * 6490391 * 2
def baseEnd_6490391 : Nat := 3332690218615621049063741

theorem tailTrace_6490391 : CollatzResearch.WordTrace tailWord_6490391 prefixEnd_6490391 3332690218615621049063741 := by
  unfold tailWord_6490391
  simp only [CollatzResearch.WordTrace]
  refine ⟨236724007429429352378063027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157816004952952901585375351 236724007429429352378063027)
  ·
    refine ⟨355086011144144028567094541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236724007429429352378063027 355086011144144028567094541)
    ·
      refine ⟨133157254179054010712660453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355086011144144028567094541 133157254179054010712660453)
      ·
        refine ⟨24966985158572627008623835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133157254179054010712660453 24966985158572627008623835)
        ·
          refine ⟨37450477737858940512935753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24966985158572627008623835 37450477737858940512935753)
          ·
            refine ⟨28087858303394205384701815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37450477737858940512935753 28087858303394205384701815)
            ·
              refine ⟨42131787455091308077052723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28087858303394205384701815 42131787455091308077052723)
              ·
                refine ⟨63197681182636962115579085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42131787455091308077052723 63197681182636962115579085)
                ·
                  refine ⟨23699130443488860793342157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63197681182636962115579085 23699130443488860793342157)
                  ·
                    refine ⟨8887173916308322797503309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23699130443488860793342157 8887173916308322797503309)
                    ·
                      refine ⟨3332690218615621049063741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8887173916308322797503309 3332690218615621049063741)
                      ·
                        rfl

theorem cell23_6490391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_6490391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490391 prefixEnd_6490391 := by exact prefixLift 6490391
  have htrace : WordTrace (prefixWord ++ tailWord_6490391) baseStart_6490391 baseEnd_6490391 := by
    simpa [prefixWord, tailWord_6490391, baseEnd_6490391] using wordTrace_append hprefix tailTrace_6490391
  have hstable : (prefixWord ++ tailWord_6490391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490391).length < 2 ^ (prefixWord ++ tailWord_6490391).sum := by decide
  have hdescent : baseEnd_6490391 < baseStart_6490391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490424 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 1, 8]
def baseStart_6490424 : Nat := 118140960795 + 6490424 * 2 ^ 59
def prefixEnd_6490424 : Nat := 4983230072969 + 3 ^ 40 * 6490424 * 2
def baseEnd_6490424 : Nat := 1110902387825739806650363

theorem tailTrace_6490424 : CollatzResearch.WordTrace tailWord_6490424 prefixEnd_6490424 1110902387825739806650363 := by
  unfold tailWord_6490424
  simp only [CollatzResearch.WordTrace]
  refine ⟨118362605519154899507007163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157816807358873199342676217 118362605519154899507007163)
  ·
    refine ⟨177543908278732349260510745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118362605519154899507007163 177543908278732349260510745)
    ·
      refine ⟨133157931209049261945383059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177543908278732349260510745 133157931209049261945383059)
      ·
        refine ⟨199736896813573892918074589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133157931209049261945383059 199736896813573892918074589)
        ·
          refine ⟨74901336305090209844277971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199736896813573892918074589 74901336305090209844277971)
          ·
            refine ⟨112352004457635314766416957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74901336305090209844277971 112352004457635314766416957)
            ·
              refine ⟨42132001671613243037406359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112352004457635314766416957 42132001671613243037406359)
              ·
                refine ⟨63198002507419864556109539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42132001671613243037406359 63198002507419864556109539)
                ·
                  refine ⟨94797003761129796834164309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63198002507419864556109539 94797003761129796834164309)
                  ·
                    refine ⟨1110902387825739806650363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94797003761129796834164309 1110902387825739806650363)
                    ·
                      rfl

theorem cell23_6490424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 1, 8].length) (baseStart_6490424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490424 prefixEnd_6490424 := by exact prefixLift 6490424
  have htrace : WordTrace (prefixWord ++ tailWord_6490424) baseStart_6490424 baseEnd_6490424 := by
    simpa [prefixWord, tailWord_6490424, baseEnd_6490424] using wordTrace_append hprefix tailTrace_6490424
  have hstable : (prefixWord ++ tailWord_6490424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490424).length < 2 ^ (prefixWord ++ tailWord_6490424).sum := by decide
  have hdescent : baseEnd_6490424 < baseStart_6490424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490425 : List Nat := [1, 2, 1, 6, 1, 1, 2, 3, 2, 1, 3]
def baseStart_6490425 : Nat := 118140960795 + 6490425 * 2 ^ 59
def prefixEnd_6490425 : Nat := 4983230072969 + 3 ^ 40 * 6490425 * 2
def baseEnd_6490425 : Nat := 3332707676957873916038585

theorem tailTrace_6490425 : CollatzResearch.WordTrace tailWord_6490425 prefixEnd_6490425 3332707676957873916038585 := by
  unfold tailWord_6490425
  simp only [CollatzResearch.WordTrace]
  refine ⟨236725247511306176184800729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157816831674204117456533819 236725247511306176184800729)
  ·
    refine ⟨177543935633479632138600547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236725247511306176184800729 177543935633479632138600547)
    ·
      refine ⟨266315903450219448207900821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177543935633479632138600547 266315903450219448207900821)
      ·
        refine ⟨12483557974229036634745351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 266315903450219448207900821 12483557974229036634745351)
        ·
          refine ⟨18725336961343554952118027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12483557974229036634745351 18725336961343554952118027)
          ·
            refine ⟨28088005442015332428177041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18725336961343554952118027 28088005442015332428177041)
            ·
              refine ⟨21066004081511499321132781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28088005442015332428177041 21066004081511499321132781)
              ·
                refine ⟨7899751530566812245424793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21066004081511499321132781 7899751530566812245424793)
                ·
                  refine ⟨5924813647925109184068595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7899751530566812245424793 5924813647925109184068595)
                  ·
                    refine ⟨8887220471887663776102893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5924813647925109184068595 8887220471887663776102893)
                    ·
                      refine ⟨3332707676957873916038585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8887220471887663776102893 3332707676957873916038585)
                      ·
                        rfl

theorem cell23_6490425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_6490425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490425 prefixEnd_6490425 := by exact prefixLift 6490425
  have htrace : WordTrace (prefixWord ++ tailWord_6490425) baseStart_6490425 baseEnd_6490425 := by
    simpa [prefixWord, tailWord_6490425, baseEnd_6490425] using wordTrace_append hprefix tailTrace_6490425
  have hstable : (prefixWord ++ tailWord_6490425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490425).length < 2 ^ (prefixWord ++ tailWord_6490425).sum := by decide
  have hdescent : baseEnd_6490425 < baseStart_6490425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490448 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 1, 4, 2]
def baseStart_6490448 : Nat := 118140960795 + 6490448 * 2 ^ 59
def prefixEnd_6490448 : Nat := 4983230072969 + 3 ^ 40 * 6490448 * 2
def baseEnd_6490448 : Nat := 3332719487012927326050979

theorem tailTrace_6490448 : CollatzResearch.WordTrace tailWord_6490448 prefixEnd_6490448 3332719487012927326050979 := by
  unfold tailWord_6490448
  simp only [CollatzResearch.WordTrace]
  refine ⟨118363043195111425556443999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157817390926815234075258665 118363043195111425556443999)
  ·
    refine ⟨177544564792667138334665999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118363043195111425556443999 177544564792667138334665999)
    ·
      refine ⟨266316847189000707501998999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177544564792667138334665999 266316847189000707501998999)
      ·
        refine ⟨399475270783501061252998499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266316847189000707501998999 399475270783501061252998499)
        ·
          refine ⟨599212906175251591879497749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399475270783501061252998499 599212906175251591879497749)
          ·
            refine ⟨28088104976964918369351457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 599212906175251591879497749 28088104976964918369351457)
            ·
              refine ⟨21066078732723688777013593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28088104976964918369351457 21066078732723688777013593)
              ·
                refine ⟨15799559049542766582760195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21066078732723688777013593 15799559049542766582760195)
                ·
                  refine ⟨23699338574314149874140293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15799559049542766582760195 23699338574314149874140293)
                  ·
                    refine ⟨4443625982683903101401305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23699338574314149874140293 4443625982683903101401305)
                    ·
                      refine ⟨3332719487012927326050979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4443625982683903101401305 3332719487012927326050979)
                      ·
                        rfl

theorem cell23_6490448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 1, 4, 2].length) (baseStart_6490448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490448 prefixEnd_6490448 := by exact prefixLift 6490448
  have htrace : WordTrace (prefixWord ++ tailWord_6490448) baseStart_6490448 baseEnd_6490448 := by
    simpa [prefixWord, tailWord_6490448, baseEnd_6490448] using wordTrace_append hprefix tailTrace_6490448
  have hstable : (prefixWord ++ tailWord_6490448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490448).length < 2 ^ (prefixWord ++ tailWord_6490448).sum := by decide
  have hdescent : baseEnd_6490448 < baseStart_6490448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490452 : List Nat := [2, 4, 1, 1, 2, 2, 4, 1, 1, 3, 2]
def baseStart_6490452 : Nat := 118140960795 + 6490452 * 2 ^ 59
def prefixEnd_6490452 : Nat := 4983230072969 + 3 ^ 40 * 6490452 * 2
def baseEnd_6490452 : Nat := 3332721540935545310400961

theorem tailTrace_6490452 : CollatzResearch.WordTrace tailWord_6490452 prefixEnd_6490452 3332721540935545310400961 := by
  unfold tailWord_6490452
  simp only [CollatzResearch.WordTrace]
  refine ⟨118363116141104179898016805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157817488188138906530689073 118363116141104179898016805)
  ·
    refine ⟨22193084276457033730878151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118363116141104179898016805 22193084276457033730878151)
    ·
      refine ⟨33289626414685550596317227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22193084276457033730878151 33289626414685550596317227)
      ·
        refine ⟨49934439622028325894475841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33289626414685550596317227 49934439622028325894475841)
        ·
          refine ⟨37450829716521244420856881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49934439622028325894475841 37450829716521244420856881)
          ·
            refine ⟨28088122287390933315642661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37450829716521244420856881 28088122287390933315642661)
            ·
              refine ⟨5266522928885799996682999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28088122287390933315642661 5266522928885799996682999)
              ·
                refine ⟨7899784393328699995024499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5266522928885799996682999 7899784393328699995024499)
                ·
                  refine ⟨11849676589993049992536749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7899784393328699995024499 11849676589993049992536749)
                  ·
                    refine ⟨4443628721247393747201281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11849676589993049992536749 4443628721247393747201281)
                    ·
                      refine ⟨3332721540935545310400961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4443628721247393747201281 3332721540935545310400961)
                      ·
                        rfl

theorem cell23_6490452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_6490452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490452 prefixEnd_6490452 := by exact prefixLift 6490452
  have htrace : WordTrace (prefixWord ++ tailWord_6490452) baseStart_6490452 baseEnd_6490452 := by
    simpa [prefixWord, tailWord_6490452, baseEnd_6490452] using wordTrace_append hprefix tailTrace_6490452
  have hstable : (prefixWord ++ tailWord_6490452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490452).length < 2 ^ (prefixWord ++ tailWord_6490452).sum := by decide
  have hdescent : baseEnd_6490452 < baseStart_6490452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490471 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 7]
def baseStart_6490471 : Nat := 118140960795 + 6490471 * 2 ^ 59
def prefixEnd_6490471 : Nat := 4983230072969 + 3 ^ 40 * 6490471 * 2
def baseEnd_6490471 : Nat := 370303477451997859562597

theorem tailTrace_6490471 : CollatzResearch.WordTrace tailWord_6490471 prefixEnd_6490471 370303477451997859562597 := by
  unfold tailWord_6490471
  simp only [CollatzResearch.WordTrace]
  refine ⟨236726925269139526040975267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157817950179426350693983511 236726925269139526040975267)
  ·
    refine ⟨355090387903709289061462901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236726925269139526040975267 355090387903709289061462901)
    ·
      refine ⟨33289723865972745849512147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 355090387903709289061462901 33289723865972745849512147)
      ·
        refine ⟨49934585798959118774268221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33289723865972745849512147 49934585798959118774268221)
        ·
          refine ⟨18725469674609669540350583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49934585798959118774268221 18725469674609669540350583)
          ·
            refine ⟨28088204511914504310525875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18725469674609669540350583 28088204511914504310525875)
            ·
              refine ⟨42132306767871756465788813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28088204511914504310525875 42132306767871756465788813)
              ·
                refine ⟨15799615037951908674670805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42132306767871756465788813 15799615037951908674670805)
                ·
                  refine ⟨370303477451997859562597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15799615037951908674670805 370303477451997859562597)
                  ·
                    rfl

theorem cell23_6490471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 7].length) (baseStart_6490471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490471 prefixEnd_6490471 := by exact prefixLift 6490471
  have htrace : WordTrace (prefixWord ++ tailWord_6490471) baseStart_6490471 baseEnd_6490471 := by
    simpa [prefixWord, tailWord_6490471, baseEnd_6490471] using wordTrace_append hprefix tailTrace_6490471
  have hstable : (prefixWord ++ tailWord_6490471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490471).length < 2 ^ (prefixWord ++ tailWord_6490471).sum := by decide
  have hdescent : baseEnd_6490471 < baseStart_6490471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490501 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 2, 5]
def baseStart_6490501 : Nat := 118140960795 + 6490501 * 2 ^ 59
def prefixEnd_6490501 : Nat := 4983230072969 + 3 ^ 40 * 6490501 * 2
def baseEnd_6490501 : Nat := 1110915567162538539562745

theorem tailTrace_6490501 : CollatzResearch.WordTrace tailWord_6490501 prefixEnd_6490501 1110915567162538539562745 := by
  unfold tailWord_6490501
  simp only [CollatzResearch.WordTrace]
  refine ⟨236728019459030841164567357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157818679639353894109711571 236728019459030841164567357)
  ·
    refine ⟨88773007297136565436712759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236728019459030841164567357 88773007297136565436712759)
    ·
      refine ⟨133159510945704848155069139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88773007297136565436712759 133159510945704848155069139)
      ·
        refine ⟨199739266418557272232603709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133159510945704848155069139 199739266418557272232603709)
        ·
          refine ⟨74902224906958977087226391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199739266418557272232603709 74902224906958977087226391)
          ·
            refine ⟨112353337360438465630839587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74902224906958977087226391 112353337360438465630839587)
            ·
              refine ⟨168530006040657698446259381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112353337360438465630839587 168530006040657698446259381)
              ·
                refine ⟨15799688066311659229336817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168530006040657698446259381 15799688066311659229336817)
                ·
                  refine ⟨11849766049733744422002613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15799688066311659229336817 11849766049733744422002613)
                  ·
                    refine ⟨1110915567162538539562745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11849766049733744422002613 1110915567162538539562745)
                    ·
                      rfl

theorem cell23_6490501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 2, 5].length) (baseStart_6490501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490501 prefixEnd_6490501 := by exact prefixLift 6490501
  have htrace : WordTrace (prefixWord ++ tailWord_6490501) baseStart_6490501 baseEnd_6490501 := by
    simpa [prefixWord, tailWord_6490501, baseEnd_6490501] using wordTrace_append hprefix tailTrace_6490501
  have hstable : (prefixWord ++ tailWord_6490501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490501).length < 2 ^ (prefixWord ++ tailWord_6490501).sum := by decide
  have hdescent : baseEnd_6490501 < baseStart_6490501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490505 : List Nat := [1, 2, 1, 1, 6, 3, 1, 3, 5]
def baseStart_6490505 : Nat := 118140960795 + 6490505 * 2 ^ 59
def prefixEnd_6490505 : Nat := 4983230072969 + 3 ^ 40 * 6490505 * 2
def baseEnd_6490505 : Nat := 370305417267803733670913

theorem tailTrace_6490505 : CollatzResearch.WordTrace tailWord_6490505 prefixEnd_6490505 370305417267803733670913 := by
  unfold tailWord_6490505
  simp only [CollatzResearch.WordTrace]
  refine ⟨236728165351016349847712969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157818776900677566565141979 236728165351016349847712969)
  ·
    refine ⟨177546124013262262385784727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236728165351016349847712969 177546124013262262385784727)
    ·
      refine ⟨266319186019893393578677091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177546124013262262385784727 266319186019893393578677091)
      ·
        refine ⟨399478779029840090368015637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266319186019893393578677091 399478779029840090368015637)
        ·
          refine ⟨18725567767023754236000733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 399478779029840090368015637 18725567767023754236000733)
          ·
            refine ⟨7022087912633907838500275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18725567767023754236000733 7022087912633907838500275)
            ·
              refine ⟨10533131868950861757750413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7022087912633907838500275 10533131868950861757750413)
              ·
                refine ⟨3949924450856573159156405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10533131868950861757750413 3949924450856573159156405)
                ·
                  refine ⟨370305417267803733670913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3949924450856573159156405 370305417267803733670913)
                  ·
                    rfl

theorem cell23_6490505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 5].length) (baseStart_6490505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490505 prefixEnd_6490505 := by exact prefixLift 6490505
  have htrace : WordTrace (prefixWord ++ tailWord_6490505) baseStart_6490505 baseEnd_6490505 := by
    simpa [prefixWord, tailWord_6490505, baseEnd_6490505] using wordTrace_append hprefix tailTrace_6490505
  have hstable : (prefixWord ++ tailWord_6490505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490505).length < 2 ^ (prefixWord ++ tailWord_6490505).sum := by decide
  have hdescent : baseEnd_6490505 < baseStart_6490505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490558 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_6490558 : Nat := 118140960795 + 6490558 * 2 ^ 59
def prefixEnd_6490558 : Nat := 4983230072969 + 3 ^ 40 * 6490558 * 2
def baseEnd_6490558 : Nat := 3332775969884921895675473

theorem tailTrace_6490558 : CollatzResearch.WordTrace tailWord_6490558 prefixEnd_6490558 3332775969884921895675473 := by
  unfold tailWord_6490558
  simp only [CollatzResearch.WordTrace]
  refine ⟨29591262302478042487424041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157820065613216226599594885 29591262302478042487424041)
  ·
    refine ⟨22193446726858531865568031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29591262302478042487424041 22193446726858531865568031)
    ·
      refine ⟨33290170090287797798352047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22193446726858531865568031 33290170090287797798352047)
      ·
        refine ⟨49935255135431696697528071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33290170090287797798352047 49935255135431696697528071)
        ·
          refine ⟨74902882703147545046292107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49935255135431696697528071 74902882703147545046292107)
          ·
            refine ⟨112354324054721317569438161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74902882703147545046292107 112354324054721317569438161)
            ·
              refine ⟨84265743041040988177078621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112354324054721317569438161 84265743041040988177078621)
              ·
                refine ⟨31599653640390370566404483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84265743041040988177078621 31599653640390370566404483)
                ·
                  refine ⟨47399480460585555849606725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31599653640390370566404483 47399480460585555849606725)
                  ·
                    refine ⟨8887402586359791721801261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47399480460585555849606725 8887402586359791721801261)
                    ·
                      refine ⟨3332775969884921895675473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8887402586359791721801261 3332775969884921895675473)
                      ·
                        rfl

theorem cell23_6490558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_6490558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490558 prefixEnd_6490558 := by exact prefixLift 6490558
  have htrace : WordTrace (prefixWord ++ tailWord_6490558) baseStart_6490558 baseEnd_6490558 := by
    simpa [prefixWord, tailWord_6490558, baseEnd_6490558] using wordTrace_append hprefix tailTrace_6490558
  have hstable : (prefixWord ++ tailWord_6490558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490558).length < 2 ^ (prefixWord ++ tailWord_6490558).sum := by decide
  have hdescent : baseEnd_6490558 < baseStart_6490558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490608 : List Nat := [2, 1, 1, 1, 3, 3, 2, 4, 1, 5]
def baseStart_6490608 : Nat := 118140960795 + 6490608 * 2 ^ 59
def prefixEnd_6490608 : Nat := 4983230072969 + 3 ^ 40 * 6490608 * 2
def baseEnd_6490608 : Nat := 1110933881305882233350081

theorem tailTrace_6490608 : CollatzResearch.WordTrace tailWord_6490608 prefixEnd_6490608 1110933881305882233350081 := by
  unfold tailWord_6490608
  simp only [CollatzResearch.WordTrace]
  refine ⟨118365961034821599219356239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157821281379762132292474985 118365961034821599219356239)
  ·
    refine ⟨177548941552232398829034359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118365961034821599219356239 177548941552232398829034359)
    ·
      refine ⟨266323412328348598243551539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177548941552232398829034359 266323412328348598243551539)
      ·
        refine ⟨399485118492522897365327309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266323412328348598243551539 399485118492522897365327309)
        ·
          refine ⟨149806919434696086511997741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399485118492522897365327309 149806919434696086511997741)
          ·
            refine ⟨56177594788011032441999153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149806919434696086511997741 56177594788011032441999153)
            ·
              refine ⟨42133196091008274331499365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56177594788011032441999153 42133196091008274331499365)
              ·
                refine ⟨7899974267064051437156131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42133196091008274331499365 7899974267064051437156131)
                ·
                  refine ⟨11849961400596077155734197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7899974267064051437156131 11849961400596077155734197)
                  ·
                    refine ⟨1110933881305882233350081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11849961400596077155734197 1110933881305882233350081)
                    ·
                      rfl

theorem cell23_6490608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 1, 5].length) (baseStart_6490608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490608 prefixEnd_6490608 := by exact prefixLift 6490608
  have htrace : WordTrace (prefixWord ++ tailWord_6490608) baseStart_6490608 baseEnd_6490608 := by
    simpa [prefixWord, tailWord_6490608, baseEnd_6490608] using wordTrace_append hprefix tailTrace_6490608
  have hstable : (prefixWord ++ tailWord_6490608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490608).length < 2 ^ (prefixWord ++ tailWord_6490608).sum := by decide
  have hdescent : baseEnd_6490608 < baseStart_6490608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490625 : List Nat := [1, 2, 4, 1, 3, 2, 1, 3, 1, 5]
def baseStart_6490625 : Nat := 118140960795 + 6490625 * 2 ^ 59
def prefixEnd_6490625 : Nat := 4983230072969 + 3 ^ 40 * 6490625 * 2
def baseEnd_6490625 : Nat := 1110936791029591044512555

theorem tailTrace_6490625 : CollatzResearch.WordTrace tailWord_6490625 prefixEnd_6490625 1110936791029591044512555 := by
  unfold tailWord_6490625
  simp only [CollatzResearch.WordTrace]
  refine ⟨236732542110581610342081329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157821694740387740228054219 236732542110581610342081329)
  ·
    refine ⟨177549406582936207756560997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236732542110581610342081329 177549406582936207756560997)
    ·
      refine ⟨33290513734300538954355187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177549406582936207756560997 33290513734300538954355187)
      ·
        refine ⟨49935770601450808431532781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33290513734300538954355187 49935770601450808431532781)
        ·
          refine ⟨18725913975544053161824793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49935770601450808431532781 18725913975544053161824793)
          ·
            refine ⟨14044435481658039871368595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18725913975544053161824793 14044435481658039871368595)
            ·
              refine ⟨21066653222487059807052893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14044435481658039871368595 21066653222487059807052893)
              ·
                refine ⟨7899994958432647427644835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21066653222487059807052893 7899994958432647427644835)
                ·
                  refine ⟨11849992437648971141467253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7899994958432647427644835 11849992437648971141467253)
                  ·
                    refine ⟨1110936791029591044512555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11849992437648971141467253 1110936791029591044512555)
                    ·
                      rfl

theorem cell23_6490625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_6490625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490625 prefixEnd_6490625 := by exact prefixLift 6490625
  have htrace : WordTrace (prefixWord ++ tailWord_6490625) baseStart_6490625 baseEnd_6490625 := by
    simpa [prefixWord, tailWord_6490625, baseEnd_6490625] using wordTrace_append hprefix tailTrace_6490625
  have hstable : (prefixWord ++ tailWord_6490625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490625).length < 2 ^ (prefixWord ++ tailWord_6490625).sum := by decide
  have hdescent : baseEnd_6490625 < baseStart_6490625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490648 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 3, 1, 5]
def baseStart_6490648 : Nat := 118140960795 + 6490648 * 2 ^ 59
def prefixEnd_6490648 : Nat := 4983230072969 + 3 ^ 40 * 6490648 * 2
def baseEnd_6490648 : Nat := 3332822183143826543550059

theorem tailTrace_6490648 : CollatzResearch.WordTrace tailWord_6490648 prefixEnd_6490648 3332822183143826543550059 := by
  unfold tailWord_6490648
  simp only [CollatzResearch.WordTrace]
  refine ⟨118366690494749142635084299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157822253992998856846779065 118366690494749142635084299)
  ·
    refine ⟨177550035742123713952626449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118366690494749142635084299 177550035742123713952626449)
    ·
      refine ⟨133162526806592785464469837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177550035742123713952626449 133162526806592785464469837)
      ·
        refine ⟨49935947552472294549176189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133162526806592785464469837 49935947552472294549176189)
        ·
          refine ⟨18725980332177110455941071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49935947552472294549176189 18725980332177110455941071)
          ·
            refine ⟨28088970498265665683911607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18725980332177110455941071 28088970498265665683911607)
            ·
              refine ⟨42133455747398498525867411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28088970498265665683911607 42133455747398498525867411)
              ·
                refine ⟨63200183621097747788801117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42133455747398498525867411 63200183621097747788801117)
                ·
                  refine ⟨23700068857911655420800419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63200183621097747788801117 23700068857911655420800419)
                  ·
                    refine ⟨35550103286867483131200629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23700068857911655420800419 35550103286867483131200629)
                    ·
                      refine ⟨3332822183143826543550059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35550103286867483131200629 3332822183143826543550059)
                      ·
                        rfl

theorem cell23_6490648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 3, 1, 5].length) (baseStart_6490648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490648 prefixEnd_6490648 := by exact prefixLift 6490648
  have htrace : WordTrace (prefixWord ++ tailWord_6490648) baseStart_6490648 baseEnd_6490648 := by
    simpa [prefixWord, tailWord_6490648, baseEnd_6490648] using wordTrace_append hprefix tailTrace_6490648
  have hstable : (prefixWord ++ tailWord_6490648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490648).length < 2 ^ (prefixWord ++ tailWord_6490648).sum := by decide
  have hdescent : baseEnd_6490648 < baseStart_6490648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490671 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 6]
def baseStart_6490671 : Nat := 118140960795 + 6490671 * 2 ^ 59
def prefixEnd_6490671 : Nat := 4983230072969 + 3 ^ 40 * 6490671 * 2
def baseEnd_6490671 : Nat := 3332833993198879953562453

theorem tailTrace_6490671 : CollatzResearch.WordTrace tailWord_6490671 prefixEnd_6490671 3332833993198879953562453 := by
  unfold tailWord_6490671
  simp only [CollatzResearch.WordTrace]
  refine ⟨236734219868414960198255867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157822813245609973465503911 236734219868414960198255867)
  ·
    refine ⟨355101329802622440297383801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236734219868414960198255867 355101329802622440297383801)
    ·
      refine ⟨266325997351966830223037851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355101329802622440297383801 266325997351966830223037851)
      ·
        refine ⟨399488996027950245334556777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266325997351966830223037851 399488996027950245334556777)
        ·
          refine ⟨299616747020962684000917583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399488996027950245334556777 299616747020962684000917583)
          ·
            refine ⟨449425120531444026001376375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299616747020962684000917583 449425120531444026001376375)
            ·
              refine ⟨674137680797166039002064563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449425120531444026001376375 674137680797166039002064563)
              ·
                refine ⟨1011206521195749058503096845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674137680797166039002064563 1011206521195749058503096845)
                ·
                  refine ⟨379202445448405896938661317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1011206521195749058503096845 379202445448405896938661317)
                  ·
                    refine ⟨71100458521576105675998997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 379202445448405896938661317 71100458521576105675998997)
                    ·
                      refine ⟨3332833993198879953562453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71100458521576105675998997 3332833993198879953562453)
                      ·
                        rfl

theorem cell23_6490671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 6].length) (baseStart_6490671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490671 prefixEnd_6490671 := by exact prefixLift 6490671
  have htrace : WordTrace (prefixWord ++ tailWord_6490671) baseStart_6490671 baseEnd_6490671 := by
    simpa [prefixWord, tailWord_6490671, baseEnd_6490671] using wordTrace_append hprefix tailTrace_6490671
  have hstable : (prefixWord ++ tailWord_6490671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490671).length < 2 ^ (prefixWord ++ tailWord_6490671).sum := by decide
  have hdescent : baseEnd_6490671 < baseStart_6490671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490716 : List Nat := [2, 2, 4, 1, 4, 1, 1, 2, 1, 2, 3]
def baseStart_6490716 : Nat := 118140960795 + 6490716 * 2 ^ 59
def prefixEnd_6490716 : Nat := 4983230072969 + 3 ^ 40 * 6490716 * 2
def baseEnd_6490716 : Nat := 3332857099828332277499747

theorem tailTrace_6490716 : CollatzResearch.WordTrace tailWord_6490716 prefixEnd_6490716 3332857099828332277499747 := by
  unfold tailWord_6490716
  simp only [CollatzResearch.WordTrace]
  refine ⟨118367930576625966441822001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157823907435501288589096001 118367930576625966441822001)
  ·
    refine ⟨88775947932469474831366501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118367930576625966441822001 88775947932469474831366501)
    ·
      refine ⟨16645490237338026530881219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88775947932469474831366501 16645490237338026530881219)
      ·
        refine ⟨24968235356007039796321829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16645490237338026530881219 24968235356007039796321829)
        ·
          refine ⟨4681544129251319961810343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24968235356007039796321829 4681544129251319961810343)
          ·
            refine ⟨7022316193876979942715515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4681544129251319961810343 7022316193876979942715515)
            ·
              refine ⟨10533474290815469914073273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7022316193876979942715515 10533474290815469914073273)
              ·
                refine ⟨7900105718111602435554955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10533474290815469914073273 7900105718111602435554955)
                ·
                  refine ⟨11850158577167403653332433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7900105718111602435554955 11850158577167403653332433)
                  ·
                    refine ⟨8887618932875552739999325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11850158577167403653332433 8887618932875552739999325)
                    ·
                      refine ⟨3332857099828332277499747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8887618932875552739999325 3332857099828332277499747)
                      ·
                        rfl

theorem cell23_6490716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_6490716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490716 prefixEnd_6490716 := by exact prefixLift 6490716
  have htrace : WordTrace (prefixWord ++ tailWord_6490716) baseStart_6490716 baseEnd_6490716 := by
    simpa [prefixWord, tailWord_6490716, baseEnd_6490716] using wordTrace_append hprefix tailTrace_6490716
  have hstable : (prefixWord ++ tailWord_6490716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490716).length < 2 ^ (prefixWord ++ tailWord_6490716).sum := by decide
  have hdescent : baseEnd_6490716 < baseStart_6490716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490735 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 3, 4, 2]
def baseStart_6490735 : Nat := 118140960795 + 6490735 * 2 ^ 59
def prefixEnd_6490735 : Nat := 4983230072969 + 3 ^ 40 * 6490735 * 2
def baseEnd_6490735 : Nat := 3332866855960767703162159

theorem tailTrace_6490735 : CollatzResearch.WordTrace tailWord_6490735 prefixEnd_6490735 3332866855960767703162159 := by
  unfold tailWord_6490735
  simp only [CollatzResearch.WordTrace]
  refine ⟨236736554140183099128585659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157824369426788732752390439 236736554140183099128585659)
  ·
    refine ⟨355104831210274648692878489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236736554140183099128585659 355104831210274648692878489)
    ·
      refine ⟨266328623407705986519658867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355104831210274648692878489 266328623407705986519658867)
      ·
        refine ⟨399492935111558979779488301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266328623407705986519658867 399492935111558979779488301)
        ·
          refine ⟨149809850666834617417308113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399492935111558979779488301 149809850666834617417308113)
          ·
            refine ⟨112357388000125963062981085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149809850666834617417308113 112357388000125963062981085)
            ·
              refine ⟨42134020500047236148617907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112357388000125963062981085 42134020500047236148617907)
              ·
                refine ⟨63201030750070854222926861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42134020500047236148617907 63201030750070854222926861)
                ·
                  refine ⟨23700386531276570333597573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63201030750070854222926861 23700386531276570333597573)
                  ·
                    refine ⟨4443822474614356937549545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23700386531276570333597573 4443822474614356937549545)
                    ·
                      refine ⟨3332866855960767703162159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4443822474614356937549545 3332866855960767703162159)
                      ·
                        rfl

theorem cell23_6490735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 4, 2].length) (baseStart_6490735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490735 prefixEnd_6490735 := by exact prefixLift 6490735
  have htrace : WordTrace (prefixWord ++ tailWord_6490735) baseStart_6490735 baseEnd_6490735 := by
    simpa [prefixWord, tailWord_6490735, baseEnd_6490735] using wordTrace_append hprefix tailTrace_6490735
  have hstable : (prefixWord ++ tailWord_6490735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490735).length < 2 ^ (prefixWord ++ tailWord_6490735).sum := by decide
  have hdescent : baseEnd_6490735 < baseStart_6490735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490862 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_6490862 : Nat := 118140960795 + 6490862 * 2 ^ 59
def prefixEnd_6490862 : Nat := 4983230072969 + 3 ^ 40 * 6490862 * 2
def baseEnd_6490862 : Nat := 3332932068003888706274075

theorem tailTrace_6490862 : CollatzResearch.WordTrace tailWord_6490862 prefixEnd_6490862 3332932068003888706274075 := by
  unfold tailWord_6490862
  simp only [CollatzResearch.WordTrace]
  refine ⟨29592648276340374977307355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157827457473815333212305893 29592648276340374977307355)
  ·
    refine ⟨44388972414510562465961033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29592648276340374977307355 44388972414510562465961033)
    ·
      refine ⟨33291729310882921849470775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44388972414510562465961033 33291729310882921849470775)
      ·
        refine ⟨49937593966324382774206163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33291729310882921849470775 49937593966324382774206163)
        ·
          refine ⟨74906390949486574161309245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49937593966324382774206163 74906390949486574161309245)
          ·
            refine ⟨28089896606057465310490967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74906390949486574161309245 28089896606057465310490967)
            ·
              refine ⟨42134844909086197965736451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28089896606057465310490967 42134844909086197965736451)
              ·
                refine ⟨63202267363629296948604677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42134844909086197965736451 63202267363629296948604677)
                ·
                  refine ⟨11850425130680493177863377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63202267363629296948604677 11850425130680493177863377)
                  ·
                    refine ⟨8887818848010369883397533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11850425130680493177863377 8887818848010369883397533)
                    ·
                      refine ⟨3332932068003888706274075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8887818848010369883397533 3332932068003888706274075)
                      ·
                        rfl

theorem cell23_6490862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_6490862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490862 prefixEnd_6490862 := by exact prefixLift 6490862
  have htrace : WordTrace (prefixWord ++ tailWord_6490862) baseStart_6490862 baseEnd_6490862 := by
    simpa [prefixWord, tailWord_6490862, baseEnd_6490862] using wordTrace_append hprefix tailTrace_6490862
  have hstable : (prefixWord ++ tailWord_6490862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490862).length < 2 ^ (prefixWord ++ tailWord_6490862).sum := by decide
  have hdescent : baseEnd_6490862 < baseStart_6490862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490865 : List Nat := [1, 2, 2, 2, 2, 2, 2, 4, 6]
def baseStart_6490865 : Nat := 118140960795 + 6490865 * 2 ^ 59
def prefixEnd_6490865 : Nat := 4983230072969 + 3 ^ 40 * 6490865 * 2
def baseEnd_6490865 : Nat := 370325956493983577170729

theorem tailTrace_6490865 : CollatzResearch.WordTrace tailWord_6490865 prefixEnd_6490865 370325956493983577170729 := by
  unfold tailWord_6490865
  simp only [CollatzResearch.WordTrace]
  refine ⟨236741295629712131330818049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157827530419808087553878699 236741295629712131330818049)
  ·
    refine ⟨177555971722284098498113537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236741295629712131330818049 177555971722284098498113537)
    ·
      refine ⟨133166978791713073873585153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177555971722284098498113537 133166978791713073873585153)
      ·
        refine ⟨99875234093784805405188865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133166978791713073873585153 99875234093784805405188865)
        ·
          refine ⟨74906425570338604053891649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99875234093784805405188865 74906425570338604053891649)
          ·
            refine ⟨56179819177753953040418737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74906425570338604053891649 56179819177753953040418737)
            ·
              refine ⟨42134864383315464780314053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56179819177753953040418737 42134864383315464780314053)
              ·
                refine ⟨7900287071871649646308885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42134864383315464780314053 7900287071871649646308885)
                ·
                  refine ⟨370325956493983577170729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7900287071871649646308885 370325956493983577170729)
                  ·
                    rfl

theorem cell23_6490865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 6].length) (baseStart_6490865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490865 prefixEnd_6490865 := by exact prefixLift 6490865
  have htrace : WordTrace (prefixWord ++ tailWord_6490865) baseStart_6490865 baseEnd_6490865 := by
    simpa [prefixWord, tailWord_6490865, baseEnd_6490865] using wordTrace_append hprefix tailTrace_6490865
  have hstable : (prefixWord ++ tailWord_6490865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490865).length < 2 ^ (prefixWord ++ tailWord_6490865).sum := by decide
  have hdescent : baseEnd_6490865 < baseStart_6490865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490892 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 5, 1, 3]
def baseStart_6490892 : Nat := 118140960795 + 6490892 * 2 ^ 59
def prefixEnd_6490892 : Nat := 4983230072969 + 3 ^ 40 * 6490892 * 2
def baseEnd_6490892 : Nat := 3332947472423523588898937

theorem tailTrace_6490892 : CollatzResearch.WordTrace tailWord_6490892 prefixEnd_6490892 3332947472423523588898937 := by
  unfold tailWord_6490892
  simp only [CollatzResearch.WordTrace]
  refine ⟨118371140200307157471025465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157828186933742876628033953 118371140200307157471025465)
  ·
    refine ⟨88778355150230368103269099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118371140200307157471025465 88778355150230368103269099)
    ·
      refine ⟨133167532725345552154903649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88778355150230368103269099 133167532725345552154903649)
      ·
        refine ⟨99875649544009164116177737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133167532725345552154903649 99875649544009164116177737)
        ·
          refine ⟨74906737158006873087133303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99875649544009164116177737 74906737158006873087133303)
          ·
            refine ⟨112360105737010309630699955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74906737158006873087133303 112360105737010309630699955)
            ·
              refine ⟨168540158605515464446049933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112360105737010309630699955 168540158605515464446049933)
              ·
                refine ⟨63202559477068299167268725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168540158605515464446049933 63202559477068299167268725)
                ·
                  refine ⟨5925239950975153046931443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63202559477068299167268725 5925239950975153046931443)
                  ·
                    refine ⟨8887859926462729570397165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5925239950975153046931443 8887859926462729570397165)
                    ·
                      refine ⟨3332947472423523588898937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8887859926462729570397165 3332947472423523588898937)
                      ·
                        rfl

theorem cell23_6490892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_6490892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490892 prefixEnd_6490892 := by exact prefixLift 6490892
  have htrace : WordTrace (prefixWord ++ tailWord_6490892) baseStart_6490892 baseEnd_6490892 := by
    simpa [prefixWord, tailWord_6490892, baseEnd_6490892] using wordTrace_append hprefix tailTrace_6490892
  have hstable : (prefixWord ++ tailWord_6490892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490892).length < 2 ^ (prefixWord ++ tailWord_6490892).sum := by decide
  have hdescent : baseEnd_6490892 < baseStart_6490892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490895 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 3, 5]
def baseStart_6490895 : Nat := 118140960795 + 6490895 * 2 ^ 59
def prefixEnd_6490895 : Nat := 4983230072969 + 3 ^ 40 * 6490895 * 2
def baseEnd_6490895 : Nat := 1110983004288495692387141

theorem tailTrace_6490895 : CollatzResearch.WordTrace tailWord_6490895 prefixEnd_6490895 1110983004288495692387141 := by
  unfold tailWord_6490895
  simp only [CollatzResearch.WordTrace]
  refine ⟨236742389819603446454410139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157828259879735630969606759 236742389819603446454410139)
  ·
    refine ⟨355113584729405169681615209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236742389819603446454410139 355113584729405169681615209)
    ·
      refine ⟨266335188547053877261211407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355113584729405169681615209 266335188547053877261211407)
      ·
        refine ⟨399502782820580815891817111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266335188547053877261211407 399502782820580815891817111)
        ·
          refine ⟨599254174230871223837725667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399502782820580815891817111 599254174230871223837725667)
          ·
            refine ⟨898881261346306835756588501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599254174230871223837725667 898881261346306835756588501)
            ·
              refine ⟨21067529562804066463045043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 898881261346306835756588501 21067529562804066463045043)
              ·
                refine ⟨31601294344206099694567565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21067529562804066463045043 31601294344206099694567565)
                ·
                  refine ⟨11850485379077287385462837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31601294344206099694567565 11850485379077287385462837)
                  ·
                    refine ⟨1110983004288495692387141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11850485379077287385462837 1110983004288495692387141)
                    ·
                      rfl

theorem cell23_6490895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 3, 5].length) (baseStart_6490895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490895 prefixEnd_6490895 := by exact prefixLift 6490895
  have htrace : WordTrace (prefixWord ++ tailWord_6490895) baseStart_6490895 baseEnd_6490895 := by
    simpa [prefixWord, tailWord_6490895, baseEnd_6490895] using wordTrace_append hprefix tailTrace_6490895
  have hstable : (prefixWord ++ tailWord_6490895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490895).length < 2 ^ (prefixWord ++ tailWord_6490895).sum := by decide
  have hdescent : baseEnd_6490895 < baseStart_6490895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490935 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 5]
def baseStart_6490935 : Nat := 118140960795 + 6490935 * 2 ^ 59
def prefixEnd_6490935 : Nat := 4983230072969 + 3 ^ 40 * 6490935 * 2
def baseEnd_6490935 : Nat := 3332969552091666920661239

theorem tailTrace_6490935 : CollatzResearch.WordTrace tailWord_6490935 prefixEnd_6490935 3332969552091666920661239 := by
  unfold tailWord_6490935
  simp only [CollatzResearch.WordTrace]
  refine ⟨236743848739458533285866259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157829232492972355523910839 236743848739458533285866259)
  ·
    refine ⟨355115773109187799928799389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236743848739458533285866259 355115773109187799928799389)
    ·
      refine ⟨133168414915945424973299771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355115773109187799928799389 133168414915945424973299771)
      ·
        refine ⟨199752622373918137459949657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133168414915945424973299771 199752622373918137459949657)
        ·
          refine ⟨149814466780438603094962243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199752622373918137459949657 149814466780438603094962243)
          ·
            refine ⟨224721700170657904642443365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149814466780438603094962243 224721700170657904642443365)
            ·
              refine ⟨42135318781998357120458131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224721700170657904642443365 42135318781998357120458131)
              ·
                refine ⟨63202978172997535680687197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42135318781998357120458131 63202978172997535680687197)
                ·
                  refine ⟨23701116814874075880257699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63202978172997535680687197 23701116814874075880257699)
                  ·
                    refine ⟨35551675222311113820386549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23701116814874075880257699 35551675222311113820386549)
                    ·
                      refine ⟨3332969552091666920661239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35551675222311113820386549 3332969552091666920661239)
                      ·
                        rfl

theorem cell23_6490935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 5].length) (baseStart_6490935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490935 prefixEnd_6490935 := by exact prefixLift 6490935
  have htrace : WordTrace (prefixWord ++ tailWord_6490935) baseStart_6490935 baseEnd_6490935 := by
    simpa [prefixWord, tailWord_6490935, baseEnd_6490935] using wordTrace_append hprefix tailTrace_6490935
  have hstable : (prefixWord ++ tailWord_6490935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490935).length < 2 ^ (prefixWord ++ tailWord_6490935).sum := by decide
  have hdescent : baseEnd_6490935 < baseStart_6490935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490952 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 3, 2, 3]
def baseStart_6490952 : Nat := 118140960795 + 6490952 * 2 ^ 59
def prefixEnd_6490952 : Nat := 4983230072969 + 3 ^ 40 * 6490952 * 2
def baseEnd_6490952 : Nat := 3332978281262793354148661

theorem tailTrace_6490952 : CollatzResearch.WordTrace tailWord_6490952 prefixEnd_6490952 3332978281262793354148661 := by
  unfold tailWord_6490952
  simp only [CollatzResearch.WordTrace]
  refine ⟨118372234390198472594617555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157829645853597963459490073 118372234390198472594617555)
  ·
    refine ⟨177558351585297708891926333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118372234390198472594617555 177558351585297708891926333)
    ·
      refine ⟨66584381844486640834472375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177558351585297708891926333 66584381844486640834472375)
      ·
        refine ⟨99876572766729961251708563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66584381844486640834472375 99876572766729961251708563)
        ·
          refine ⟨149814859150094941877562845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99876572766729961251708563 149814859150094941877562845)
          ·
            refine ⟨56180572181285603204086067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149814859150094941877562845 56180572181285603204086067)
            ·
              refine ⟨84270858271928404806129101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56180572181285603204086067 84270858271928404806129101)
              ·
                refine ⟨31601571851973151802298413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84270858271928404806129101 31601571851973151802298413)
                ·
                  refine ⟨11850589444489931925861905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31601571851973151802298413 11850589444489931925861905)
                  ·
                    refine ⟨8887942083367448944396429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11850589444489931925861905 8887942083367448944396429)
                    ·
                      refine ⟨3332978281262793354148661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8887942083367448944396429 3332978281262793354148661)
                      ·
                        rfl

theorem cell23_6490952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_6490952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490952 prefixEnd_6490952 := by exact prefixLift 6490952
  have htrace : WordTrace (prefixWord ++ tailWord_6490952) baseStart_6490952 baseEnd_6490952 := by
    simpa [prefixWord, tailWord_6490952, baseEnd_6490952] using wordTrace_append hprefix tailTrace_6490952
  have hstable : (prefixWord ++ tailWord_6490952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490952).length < 2 ^ (prefixWord ++ tailWord_6490952).sum := by decide
  have hdescent : baseEnd_6490952 < baseStart_6490952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490962 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_6490962 : Nat := 118140960795 + 6490962 * 2 ^ 59
def prefixEnd_6490962 : Nat := 4983230072969 + 3 ^ 40 * 6490962 * 2
def baseEnd_6490962 : Nat := 3332983416069338315023615

theorem tailTrace_6490962 : CollatzResearch.WordTrace tailWord_6490962 prefixEnd_6490962 3332983416069338315023615 := by
  unfold tailWord_6490962
  simp only [CollatzResearch.WordTrace]
  refine ⟨59186208377590179224274785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157829889006907144598066093 59186208377590179224274785)
  ·
    refine ⟨44389656283192634418206089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59186208377590179224274785 44389656283192634418206089)
    ·
      refine ⟨33292242212394475813654567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44389656283192634418206089 33292242212394475813654567)
      ·
        refine ⟨49938363318591713720481851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33292242212394475813654567 49938363318591713720481851)
        ·
          refine ⟨74907544977887570580722777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49938363318591713720481851 74907544977887570580722777)
          ·
            refine ⟨56180658733415677935542083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74907544977887570580722777 56180658733415677935542083)
            ·
              refine ⟨84270988100123516903313125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56180658733415677935542083 84270988100123516903313125)
              ·
                refine ⟨15800810268773159419371211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84270988100123516903313125 15800810268773159419371211)
                ·
                  refine ⟨23701215403159739129056817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15800810268773159419371211 23701215403159739129056817)
                  ·
                    refine ⟨17775911552369804346792613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23701215403159739129056817 17775911552369804346792613)
                    ·
                      refine ⟨3332983416069338315023615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17775911552369804346792613 3332983416069338315023615)
                      ·
                        rfl

theorem cell23_6490962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_6490962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490962 prefixEnd_6490962 := by exact prefixLift 6490962
  have htrace : WordTrace (prefixWord ++ tailWord_6490962) baseStart_6490962 baseEnd_6490962 := by
    simpa [prefixWord, tailWord_6490962, baseEnd_6490962] using wordTrace_append hprefix tailTrace_6490962
  have hstable : (prefixWord ++ tailWord_6490962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490962).length < 2 ^ (prefixWord ++ tailWord_6490962).sum := by decide
  have hdescent : baseEnd_6490962 < baseStart_6490962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490969 : List Nat := [1, 2, 1, 2, 2, 5, 1, 3, 1, 2, 3]
def baseStart_6490969 : Nat := 118140960795 + 6490969 * 2 ^ 59
def prefixEnd_6490969 : Nat := 4983230072969 + 3 ^ 40 * 6490969 * 2
def baseEnd_6490969 : Nat := 3332987010433919787636083

theorem tailTrace_6490969 : CollatzResearch.WordTrace tailWord_6490969 prefixEnd_6490969 3332987010433919787636083 := by
  unfold tailWord_6490969
  simp only [CollatzResearch.WordTrace]
  refine ⟨236745088821335357092603961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157830059214223571395069307 236745088821335357092603961)
  ·
    refine ⟨177558816616001517819452971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236745088821335357092603961 177558816616001517819452971)
    ·
      refine ⟨266338224924002276729179457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177558816616001517819452971 266338224924002276729179457)
      ·
        refine ⟨199753668693001707546884593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266338224924002276729179457 199753668693001707546884593)
        ·
          refine ⟨149815251519751280660163445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199753668693001707546884593 149815251519751280660163445)
          ·
            refine ⟨14045179829976682561890323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 149815251519751280660163445 14045179829976682561890323)
            ·
              refine ⟨21067769744965023842835485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14045179829976682561890323 21067769744965023842835485)
              ·
                refine ⟨7900413654361883941063307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21067769744965023842835485 7900413654361883941063307)
                ·
                  refine ⟨11850620481542825911594961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7900413654361883941063307 11850620481542825911594961)
                  ·
                    refine ⟨8887965361157119433696221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11850620481542825911594961 8887965361157119433696221)
                    ·
                      refine ⟨3332987010433919787636083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8887965361157119433696221 3332987010433919787636083)
                      ·
                        rfl

theorem cell23_6490969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 2, 3].length) (baseStart_6490969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490969 prefixEnd_6490969 := by exact prefixLift 6490969
  have htrace : WordTrace (prefixWord ++ tailWord_6490969) baseStart_6490969 baseEnd_6490969 := by
    simpa [prefixWord, tailWord_6490969, baseEnd_6490969] using wordTrace_append hprefix tailTrace_6490969
  have hstable : (prefixWord ++ tailWord_6490969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490969).length < 2 ^ (prefixWord ++ tailWord_6490969).sum := by decide
  have hdescent : baseEnd_6490969 < baseStart_6490969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490972 : List Nat := [2, 2, 4, 2, 1, 2, 10]
def baseStart_6490972 : Nat := 118140960795 + 6490972 * 2 ^ 59
def prefixEnd_6490972 : Nat := 4983230072969 + 3 ^ 40 * 6490972 * 2
def baseEnd_6490972 : Nat := 41148006800936830566649

theorem tailTrace_6490972 : CollatzResearch.WordTrace tailWord_6490972 prefixEnd_6490972 41148006800936830566649 := by
  unfold tailWord_6490972
  simp only [CollatzResearch.WordTrace]
  refine ⟨118372599120162244302481585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157830132160216325736642113 118372599120162244302481585)
  ·
    refine ⟨88779449340121683226861189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118372599120162244302481585 88779449340121683226861189)
    ·
      refine ⟨16646146751272815605036473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88779449340121683226861189 16646146751272815605036473)
      ·
        refine ⟨12484610063454611703777355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16646146751272815605036473 12484610063454611703777355)
        ·
          refine ⟨18726915095181917555666033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12484610063454611703777355 18726915095181917555666033)
          ·
            refine ⟨14045186321386438166749525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18726915095181917555666033 14045186321386438166749525)
            ·
              refine ⟨41148006800936830566649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14045186321386438166749525 41148006800936830566649)
              ·
                rfl

theorem cell23_6490972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 10].length) (baseStart_6490972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490972 prefixEnd_6490972 := by exact prefixLift 6490972
  have htrace : WordTrace (prefixWord ++ tailWord_6490972) baseStart_6490972 baseEnd_6490972 := by
    simpa [prefixWord, tailWord_6490972, baseEnd_6490972] using wordTrace_append hprefix tailTrace_6490972
  have hstable : (prefixWord ++ tailWord_6490972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490972).length < 2 ^ (prefixWord ++ tailWord_6490972).sum := by decide
  have hdescent : baseEnd_6490972 < baseStart_6490972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490983 : List Nat := [1, 1, 5, 1, 2, 2, 2, 4, 1, 2, 2]
def baseStart_6490983 : Nat := 118140960795 + 6490983 * 2 ^ 59
def prefixEnd_6490983 : Nat := 4983230072969 + 3 ^ 40 * 6490983 * 2
def baseEnd_6490983 : Nat := 3332994199163082732861019

theorem tailTrace_6490983 : CollatzResearch.WordTrace tailWord_6490983 prefixEnd_6490983 3332994199163082732861019 := by
  unfold tailWord_6490983
  simp only [CollatzResearch.WordTrace]
  refine ⟨236745599443284637483613603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157830399628856424989075735 236745599443284637483613603)
  ·
    refine ⟨355118399164926956225420405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236745599443284637483613603 355118399164926956225420405)
    ·
      refine ⟨33292349921711902146133163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 355118399164926956225420405 33292349921711902146133163)
      ·
        refine ⟨49938524882567853219199745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33292349921711902146133163 49938524882567853219199745)
        ·
          refine ⟨37453893661925889914399809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49938524882567853219199745 37453893661925889914399809)
          ·
            refine ⟨28090420246444417435799857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37453893661925889914399809 28090420246444417435799857)
            ·
              refine ⟨21067815184833313076849893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28090420246444417435799857 21067815184833313076849893)
              ·
                refine ⟨3950215347156246201909355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21067815184833313076849893 3950215347156246201909355)
                ·
                  refine ⟨5925323020734369302864033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3950215347156246201909355 5925323020734369302864033)
                  ·
                    refine ⟨4443992265550776977148025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5925323020734369302864033 4443992265550776977148025)
                    ·
                      refine ⟨3332994199163082732861019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4443992265550776977148025 3332994199163082732861019)
                      ·
                        rfl

theorem cell23_6490983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_6490983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490983 prefixEnd_6490983 := by exact prefixLift 6490983
  have htrace : WordTrace (prefixWord ++ tailWord_6490983) baseStart_6490983 baseEnd_6490983 := by
    simpa [prefixWord, tailWord_6490983, baseEnd_6490983] using wordTrace_append hprefix tailTrace_6490983
  have hstable : (prefixWord ++ tailWord_6490983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490983).length < 2 ^ (prefixWord ++ tailWord_6490983).sum := by decide
  have hdescent : baseEnd_6490983 < baseStart_6490983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6490999 : List Nat := [1, 1, 3, 1, 1, 2, 1, 7, 2, 1, 3]
def baseStart_6490999 : Nat := 118140960795 + 6490999 * 2 ^ 59
def prefixEnd_6490999 : Nat := 4983230072969 + 3 ^ 40 * 6490999 * 2
def baseEnd_6490999 : Nat := 3333002414853554670260945

theorem tailTrace_6490999 : CollatzResearch.WordTrace tailWord_6490999 prefixEnd_6490999 3333002414853554670260945 := by
  unfold tailWord_6490999
  simp only [CollatzResearch.WordTrace]
  refine ⟨236746183011226672216196051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157830788674151114810797367 236746183011226672216196051)
  ·
    refine ⟨355119274516840008324294077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236746183011226672216196051 355119274516840008324294077)
    ·
      refine ⟨133169727943815003121610279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355119274516840008324294077 133169727943815003121610279)
      ·
        refine ⟨199754591915722504682415419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133169727943815003121610279 199754591915722504682415419)
        ·
          refine ⟨299631887873583757023623129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199754591915722504682415419 299631887873583757023623129)
          ·
            refine ⟨224723915905187817767717347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299631887873583757023623129 224723915905187817767717347)
            ·
              refine ⟨337085873857781726651576021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224723915905187817767717347 337085873857781726651576021)
              ·
                refine ⟨7900450168541759218396313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 337085873857781726651576021 7900450168541759218396313)
                ·
                  refine ⟨5925337626406319413797235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7900450168541759218396313 5925337626406319413797235)
                  ·
                    refine ⟨8888006439609479120695853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5925337626406319413797235 8888006439609479120695853)
                    ·
                      refine ⟨3333002414853554670260945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8888006439609479120695853 3333002414853554670260945)
                      ·
                        rfl

theorem cell23_6490999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 1, 3].length) (baseStart_6490999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6490999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6490999 prefixEnd_6490999 := by exact prefixLift 6490999
  have htrace : WordTrace (prefixWord ++ tailWord_6490999) baseStart_6490999 baseEnd_6490999 := by
    simpa [prefixWord, tailWord_6490999, baseEnd_6490999] using wordTrace_append hprefix tailTrace_6490999
  have hstable : (prefixWord ++ tailWord_6490999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6490999).length < 2 ^ (prefixWord ++ tailWord_6490999).sum := by decide
  have hdescent : baseEnd_6490999 < baseStart_6490999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6490999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491060 : List Nat := [2, 5, 2, 1, 1, 1, 3, 2, 1, 3, 2]
def baseStart_6491060 : Nat := 118140960795 + 6491060 * 2 ^ 59
def prefixEnd_6491060 : Nat := 4983230072969 + 3 ^ 40 * 6491060 * 2
def baseEnd_6491060 : Nat := 3333033737173478931598165

theorem tailTrace_6491060 : CollatzResearch.WordTrace tailWord_6491060 prefixEnd_6491060 3333033737173478931598165 := by
  unfold tailWord_6491060
  simp only [CollatzResearch.WordTrace]
  refine ⟨118374203932002839817083317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157832271909337119756111089 118374203932002839817083317)
  ·
    refine ⟨11097581618625266232851561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118374203932002839817083317 11097581618625266232851561)
    ·
      refine ⟨8323186213968949674638671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11097581618625266232851561 8323186213968949674638671)
      ·
        refine ⟨12484779320953424511958007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8323186213968949674638671 12484779320953424511958007)
        ·
          refine ⟨18727168981430136767937011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12484779320953424511958007 18727168981430136767937011)
          ·
            refine ⟨28090753472145205151905517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18727168981430136767937011 28090753472145205151905517)
            ·
              refine ⟨10534032552054451931964569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28090753472145205151905517 10534032552054451931964569)
              ·
                refine ⟨7900524414040838948973427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10534032552054451931964569 7900524414040838948973427)
                ·
                  refine ⟨11850786621061258423460141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7900524414040838948973427 11850786621061258423460141)
                  ·
                    refine ⟨4444044982897971908797553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11850786621061258423460141 4444044982897971908797553)
                    ·
                      refine ⟨3333033737173478931598165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4444044982897971908797553 3333033737173478931598165)
                      ·
                        rfl

theorem cell23_6491060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_6491060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491060 prefixEnd_6491060 := by exact prefixLift 6491060
  have htrace : WordTrace (prefixWord ++ tailWord_6491060) baseStart_6491060 baseEnd_6491060 := by
    simpa [prefixWord, tailWord_6491060, baseEnd_6491060] using wordTrace_append hprefix tailTrace_6491060
  have hstable : (prefixWord ++ tailWord_6491060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491060).length < 2 ^ (prefixWord ++ tailWord_6491060).sum := by decide
  have hdescent : baseEnd_6491060 < baseStart_6491060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491090 : List Nat := [3, 2, 2, 3, 1, 2, 2, 2, 2, 2, 2]
def baseStart_6491090 : Nat := 118140960795 + 6491090 * 2 ^ 59
def prefixEnd_6491090 : Nat := 4983230072969 + 3 ^ 40 * 6491090 * 2
def baseEnd_6491090 : Nat := 3333049141593113814223027

theorem tailTrace_6491090 : CollatzResearch.WordTrace tailWord_6491090 prefixEnd_6491090 3333049141593113814223027 := by
  unfold tailWord_6491090
  simp only [CollatzResearch.WordTrace]
  refine ⟨59187375513474248689439681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157833001369264663171839149 59187375513474248689439681)
  ·
    refine ⟨44390531635105686517079761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59187375513474248689439681 44390531635105686517079761)
    ·
      refine ⟨33292898726329264887809821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44390531635105686517079761 33292898726329264887809821)
      ·
        refine ⟨12484837022373474332928683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33292898726329264887809821 12484837022373474332928683)
        ·
          refine ⟨18727255533560211499393025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12484837022373474332928683 18727255533560211499393025)
          ·
            refine ⟨14045441650170158624544769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18727255533560211499393025 14045441650170158624544769)
            ·
              refine ⟨10534081237627618968408577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14045441650170158624544769 10534081237627618968408577)
              ·
                refine ⟨7900560928220714226306433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10534081237627618968408577 7900560928220714226306433)
                ·
                  refine ⟨5925420696165535669729825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7900560928220714226306433 5925420696165535669729825)
                  ·
                    refine ⟨4444065522124151752297369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5925420696165535669729825 4444065522124151752297369)
                    ·
                      refine ⟨3333049141593113814223027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4444065522124151752297369 3333049141593113814223027)
                      ·
                        rfl

theorem cell23_6491090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_6491090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491090 prefixEnd_6491090 := by exact prefixLift 6491090
  have htrace : WordTrace (prefixWord ++ tailWord_6491090) baseStart_6491090 baseEnd_6491090 := by
    simpa [prefixWord, tailWord_6491090, baseEnd_6491090] using wordTrace_append hprefix tailTrace_6491090
  have hstable : (prefixWord ++ tailWord_6491090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491090).length < 2 ^ (prefixWord ++ tailWord_6491090).sum := by decide
  have hdescent : baseEnd_6491090 < baseStart_6491090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491096 : List Nat := [2, 1, 2, 2, 2, 3, 4, 2, 5]
def baseStart_6491096 : Nat := 118140960795 + 6491096 * 2 ^ 59
def prefixEnd_6491096 : Nat := 4983230072969 + 3 ^ 40 * 6491096 * 2
def baseEnd_6491096 : Nat := 370339135830782310083111

theorem tailTrace_6491096 : CollatzResearch.WordTrace tailWord_6491096 prefixEnd_6491096 370339135830782310083111 := by
  unfold tailWord_6491096
  simp only [CollatzResearch.WordTrace]
  refine ⟨118374860445937628891238571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157833147261250171854984761 118374860445937628891238571)
  ·
    refine ⟨177562290668906443336857857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118374860445937628891238571 177562290668906443336857857)
    ·
      refine ⟨133171718001679832502643393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177562290668906443336857857 133171718001679832502643393)
      ·
        refine ⟨99878788501259874376982545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133171718001679832502643393 99878788501259874376982545)
        ·
          refine ⟨74909091375944905782736909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99878788501259874376982545 74909091375944905782736909)
          ·
            refine ⟨28090909265979339668526341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74909091375944905782736909 28090909265979339668526341)
            ·
              refine ⟨5267045487371126187848689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28090909265979339668526341 5267045487371126187848689)
              ·
                refine ⟨3950284115528344640886517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5267045487371126187848689 3950284115528344640886517)
                ·
                  refine ⟨370339135830782310083111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3950284115528344640886517 370339135830782310083111)
                  ·
                    rfl

theorem cell23_6491096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 5].length) (baseStart_6491096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491096 prefixEnd_6491096 := by exact prefixLift 6491096
  have htrace : WordTrace (prefixWord ++ tailWord_6491096) baseStart_6491096 baseEnd_6491096 := by
    simpa [prefixWord, tailWord_6491096, baseEnd_6491096] using wordTrace_append hprefix tailTrace_6491096
  have hstable : (prefixWord ++ tailWord_6491096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491096).length < 2 ^ (prefixWord ++ tailWord_6491096).sum := by decide
  have hdescent : baseEnd_6491096 < baseStart_6491096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491106 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_6491106 : Nat := 118140960795 + 6491106 * 2 ^ 59
def prefixEnd_6491106 : Nat := 4983230072969 + 3 ^ 40 * 6491106 * 2
def baseEnd_6491106 : Nat := 3333057357283585751622953

theorem tailTrace_6491106 : CollatzResearch.WordTrace tailWord_6491106 prefixEnd_6491106 3333057357283585751622953 := by
  unfold tailWord_6491106
  simp only [CollatzResearch.WordTrace]
  refine ⟨59187521405459757372585293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157833390414559352993560781 59187521405459757372585293)
  ·
    refine ⟨22195320527047409014719485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59187521405459757372585293 22195320527047409014719485)
    ·
      refine ⟨8323245197642778380519807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22195320527047409014719485 8323245197642778380519807)
      ·
        refine ⟨12484867796464167570779711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8323245197642778380519807 12484867796464167570779711)
        ·
          refine ⟨18727301694696251356169567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12484867796464167570779711 18727301694696251356169567)
          ·
            refine ⟨28090952542044377034254351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18727301694696251356169567 28090952542044377034254351)
            ·
              refine ⟨42136428813066565551381527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28090952542044377034254351 42136428813066565551381527)
              ·
                refine ⟨63204643219599848327072291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42136428813066565551381527 63204643219599848327072291)
                ·
                  refine ⟨94806964829399772490608437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63204643219599848327072291 94806964829399772490608437)
                  ·
                    refine ⟨8888152952756228670994541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 94806964829399772490608437 8888152952756228670994541)
                    ·
                      refine ⟨3333057357283585751622953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8888152952756228670994541 3333057357283585751622953)
                      ·
                        rfl

theorem cell23_6491106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_6491106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491106 prefixEnd_6491106 := by exact prefixLift 6491106
  have htrace : WordTrace (prefixWord ++ tailWord_6491106) baseStart_6491106 baseEnd_6491106 := by
    simpa [prefixWord, tailWord_6491106, baseEnd_6491106] using wordTrace_append hprefix tailTrace_6491106
  have hstable : (prefixWord ++ tailWord_6491106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491106).length < 2 ^ (prefixWord ++ tailWord_6491106).sum := by decide
  have hdescent : baseEnd_6491106 < baseStart_6491106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491126 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_6491126 : Nat := 118140960795 + 6491126 * 2 ^ 59
def prefixEnd_6491126 : Nat := 4983230072969 + 3 ^ 40 * 6491126 * 2
def baseEnd_6491126 : Nat := 1111022542298891891124287

theorem tailTrace_6491126 : CollatzResearch.WordTrace tailWord_6491126 prefixEnd_6491126 1111022542298891891124287 := by
  unfold tailWord_6491126
  simp only [CollatzResearch.WordTrace]
  refine ⟨14796925942610410806629327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157833876721177715270712821 14796925942610410806629327)
  ·
    refine ⟨22195388913915616209943991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14796925942610410806629327 22195388913915616209943991)
    ·
      refine ⟨33293083370873424314915987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22195388913915616209943991 33293083370873424314915987)
      ·
        refine ⟨49939625056310136472373981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33293083370873424314915987 49939625056310136472373981)
        ·
          refine ⟨18727359396116301177140243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49939625056310136472373981 18727359396116301177140243)
          ·
            refine ⟨28091039094174451765710365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18727359396116301177140243 28091039094174451765710365)
            ·
              refine ⟨10534139660315419412141387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28091039094174451765710365 10534139660315419412141387)
              ·
                refine ⟨15801209490473129118212081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10534139660315419412141387 15801209490473129118212081)
                ·
                  refine ⟨11850907117854846838659061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15801209490473129118212081 11850907117854846838659061)
                  ·
                    refine ⟨1111022542298891891124287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11850907117854846838659061 1111022542298891891124287)
                    ·
                      rfl

theorem cell23_6491126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_6491126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491126 prefixEnd_6491126 := by exact prefixLift 6491126
  have htrace : WordTrace (prefixWord ++ tailWord_6491126) baseStart_6491126 baseEnd_6491126 := by
    simpa [prefixWord, tailWord_6491126, baseEnd_6491126] using wordTrace_append hprefix tailTrace_6491126
  have hstable : (prefixWord ++ tailWord_6491126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491126).length < 2 ^ (prefixWord ++ tailWord_6491126).sum := by decide
  have hdescent : baseEnd_6491126 < baseStart_6491126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491129 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 1, 6, 2]
def baseStart_6491129 : Nat := 118140960795 + 6491129 * 2 ^ 59
def prefixEnd_6491129 : Nat := 4983230072969 + 3 ^ 40 * 6491129 * 2
def baseEnd_6491129 : Nat := 3333069167338639161635347

theorem tailTrace_6491129 : CollatzResearch.WordTrace tailWord_6491129 prefixEnd_6491129 3333069167338639161635347 := by
  unfold tailWord_6491129
  simp only [CollatzResearch.WordTrace]
  refine ⟨236750924500755704418428441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157833949667170469612285627 236750924500755704418428441)
  ·
    refine ⟨177563193375566778313821331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236750924500755704418428441 177563193375566778313821331)
    ·
      refine ⟨266344790063350167470731997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177563193375566778313821331 266344790063350167470731997)
      ·
        refine ⟨99879296273756312801524499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266344790063350167470731997 99879296273756312801524499)
        ·
          refine ⟨149818944410634469202286749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99879296273756312801524499 149818944410634469202286749)
          ·
            refine ⟨56182104153987925950857531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149818944410634469202286749 56182104153987925950857531)
            ·
              refine ⟨84273156230981888926286297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56182104153987925950857531 84273156230981888926286297)
              ·
                refine ⟨63204867173236416694714723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84273156230981888926286297 63204867173236416694714723)
                ·
                  refine ⟨94807300759854625042072085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63204867173236416694714723 94807300759854625042072085)
                  ·
                    refine ⟨4444092223118185548847129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 94807300759854625042072085 4444092223118185548847129)
                    ·
                      refine ⟨3333069167338639161635347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4444092223118185548847129 3333069167338639161635347)
                      ·
                        rfl

theorem cell23_6491129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 6, 2].length) (baseStart_6491129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491129 prefixEnd_6491129 := by exact prefixLift 6491129
  have htrace : WordTrace (prefixWord ++ tailWord_6491129) baseStart_6491129 baseEnd_6491129 := by
    simpa [prefixWord, tailWord_6491129, baseEnd_6491129] using wordTrace_append hprefix tailTrace_6491129
  have hstable : (prefixWord ++ tailWord_6491129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491129).length < 2 ^ (prefixWord ++ tailWord_6491129).sum := by decide
  have hdescent : baseEnd_6491129 < baseStart_6491129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491146 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 2, 4, 2]
def baseStart_6491146 : Nat := 118140960795 + 6491146 * 2 ^ 59
def prefixEnd_6491146 : Nat := 4983230072969 + 3 ^ 40 * 6491146 * 2
def baseEnd_6491146 : Nat := 3333077896509765595122769

theorem tailTrace_6491146 : CollatzResearch.WordTrace tailWord_6491146 prefixEnd_6491146 3333077896509765595122769 := by
  unfold tailWord_6491146
  simp only [CollatzResearch.WordTrace]
  refine ⟨59187886135423529080449323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157834363027796077547864861 59187886135423529080449323)
  ·
    refine ⟨88781829203135293620673985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59187886135423529080449323 88781829203135293620673985)
    ·
      refine ⟨66586371902351470215505489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88781829203135293620673985 66586371902351470215505489)
      ·
        refine ⟨49939778926763602661629117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66586371902351470215505489 49939778926763602661629117)
        ·
          refine ⟨18727417097536350998110919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49939778926763602661629117 18727417097536350998110919)
          ·
            refine ⟨28091125646304526497166379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18727417097536350998110919 28091125646304526497166379)
            ·
              refine ⟨42136688469456789745749569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28091125646304526497166379 42136688469456789745749569)
              ·
                refine ⟨31602516352092592309312177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42136688469456789745749569 31602516352092592309312177)
                ·
                  refine ⟨23701887264069444231984133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31602516352092592309312177 23701887264069444231984133)
                  ·
                    refine ⟨4444103862013020793497025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23701887264069444231984133 4444103862013020793497025)
                    ·
                      refine ⟨3333077896509765595122769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4444103862013020793497025 3333077896509765595122769)
                      ·
                        rfl

theorem cell23_6491146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_6491146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491146 prefixEnd_6491146 := by exact prefixLift 6491146
  have htrace : WordTrace (prefixWord ++ tailWord_6491146) baseStart_6491146 baseEnd_6491146 := by
    simpa [prefixWord, tailWord_6491146, baseEnd_6491146] using wordTrace_append hprefix tailTrace_6491146
  have hstable : (prefixWord ++ tailWord_6491146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491146).length < 2 ^ (prefixWord ++ tailWord_6491146).sum := by decide
  have hdescent : baseEnd_6491146 < baseStart_6491146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491190 : List Nat := [5, 1, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_6491190 : Nat := 118140960795 + 6491190 * 2 ^ 59
def prefixEnd_6491190 : Nat := 4983230072969 + 3 ^ 40 * 6491190 * 2
def baseEnd_6491190 : Nat := 1111033496552854474324189

theorem tailTrace_6491190 : CollatzResearch.WordTrace tailWord_6491190 prefixEnd_6491190 1111033496552854474324189 := by
  unfold tailWord_6491190
  simp only [CollatzResearch.WordTrace]
  refine ⟨14797071834595919489774939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157835432902356474557599349 14797071834595919489774939)
  ·
    refine ⟨22195607751893879234662409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14797071834595919489774939 22195607751893879234662409)
    ·
      refine ⟨16646705813920409425996807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22195607751893879234662409 16646705813920409425996807)
      ·
        refine ⟨24970058720880614138995211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16646705813920409425996807 24970058720880614138995211)
        ·
          refine ⟨37455088081320921208492817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24970058720880614138995211 37455088081320921208492817)
          ·
            refine ⟨28091316060990690906369613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37455088081320921208492817 28091316060990690906369613)
            ·
              refine ⟨10534243522871509089888605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28091316060990690906369613 10534243522871509089888605)
              ·
                refine ⟨3950341321076815908708227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10534243522871509089888605 3950341321076815908708227)
                ·
                  refine ⟨5925511981615223863062341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3950341321076815908708227 5925511981615223863062341)
                  ·
                    refine ⟨1111033496552854474324189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5925511981615223863062341 1111033496552854474324189)
                    ·
                      rfl

theorem cell23_6491190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_6491190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491190 prefixEnd_6491190 := by exact prefixLift 6491190
  have htrace : WordTrace (prefixWord ++ tailWord_6491190) baseStart_6491190 baseEnd_6491190 := by
    simpa [prefixWord, tailWord_6491190, baseEnd_6491190] using wordTrace_append hprefix tailTrace_6491190
  have hstable : (prefixWord ++ tailWord_6491190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491190).length < 2 ^ (prefixWord ++ tailWord_6491190).sum := by decide
  have hdescent : baseEnd_6491190 < baseStart_6491190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491246 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 1, 6]
def baseStart_6491246 : Nat := 118140960795 + 6491246 * 2 ^ 59
def prefixEnd_6491246 : Nat := 4983230072969 + 3 ^ 40 * 6491246 * 2
def baseEnd_6491246 : Nat := 1111043081525071734624103

theorem tailTrace_6491246 : CollatzResearch.WordTrace tailWord_6491246 prefixEnd_6491246 1111043081525071734624103 := by
  unfold tailWord_6491246
  simp only [CollatzResearch.WordTrace]
  refine ⟨29594398980166479175054699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157836794560887888933625061 29594398980166479175054699)
  ·
    refine ⟨44391598470249718762582049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29594398980166479175054699 44391598470249718762582049)
    ·
      refine ⟨33293698852687289071936537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44391598470249718762582049 33293698852687289071936537)
      ·
        refine ⟨24970274139515466803952403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33293698852687289071936537 24970274139515466803952403)
        ·
          refine ⟨37455411209273200205928605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24970274139515466803952403 37455411209273200205928605)
          ·
            refine ⟨14045779203477450077223227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37455411209273200205928605 14045779203477450077223227)
            ·
              refine ⟨21068668805216175115834841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14045779203477450077223227 21068668805216175115834841)
              ·
                refine ⟨15801501603912131336876131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21068668805216175115834841 15801501603912131336876131)
                ·
                  refine ⟨23702252405868197005314197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15801501603912131336876131 23702252405868197005314197)
                  ·
                    refine ⟨1111043081525071734624103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23702252405868197005314197 1111043081525071734624103)
                    ·
                      rfl

theorem cell23_6491246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_6491246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491246 prefixEnd_6491246 := by exact prefixLift 6491246
  have htrace : WordTrace (prefixWord ++ tailWord_6491246) baseStart_6491246 baseEnd_6491246 := by
    simpa [prefixWord, tailWord_6491246, baseEnd_6491246] using wordTrace_append hprefix tailTrace_6491246
  have hstable : (prefixWord ++ tailWord_6491246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491246).length < 2 ^ (prefixWord ++ tailWord_6491246).sum := by decide
  have hdescent : baseEnd_6491246 < baseStart_6491246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491256 : List Nat := [2, 1, 2, 1, 1, 1, 4, 5, 1, 2, 3]
def baseStart_6491256 : Nat := 118140960795 + 6491256 * 2 ^ 59
def prefixEnd_6491256 : Nat := 4983230072969 + 3 ^ 40 * 6491256 * 2
def baseEnd_6491256 : Nat := 3333134379381760164747263

theorem tailTrace_6491256 : CollatzResearch.WordTrace tailWord_6491256 prefixEnd_6491256 3333134379381760164747263 := by
  unfold tailWord_6491256
  simp only [CollatzResearch.WordTrace]
  refine ⟨118377778285647802554150811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157837037714197070072201081 118377778285647802554150811)
  ·
    refine ⟨177566667428471703831226217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118377778285647802554150811 177566667428471703831226217)
    ·
      refine ⟨133175000571353777873419663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177566667428471703831226217 133175000571353777873419663)
      ·
        refine ⟨199762500857030666810129495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133175000571353777873419663 199762500857030666810129495)
        ·
          refine ⟨299643751285546000215194243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199762500857030666810129495 299643751285546000215194243)
          ·
            refine ⟨449465626928319000322791365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299643751285546000215194243 449465626928319000322791365)
            ·
              refine ⟨84274805049059812560523381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 449465626928319000322791365 84274805049059812560523381)
              ·
                refine ⟨7900762973349357427549067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84274805049059812560523381 7900762973349357427549067)
                ·
                  refine ⟨11851144460024036141323601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7900762973349357427549067 11851144460024036141323601)
                  ·
                    refine ⟨8888358345018027105992701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11851144460024036141323601 8888358345018027105992701)
                    ·
                      refine ⟨3333134379381760164747263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8888358345018027105992701 3333134379381760164747263)
                      ·
                        rfl

theorem cell23_6491256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 1, 2, 3].length) (baseStart_6491256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491256 prefixEnd_6491256 := by exact prefixLift 6491256
  have htrace : WordTrace (prefixWord ++ tailWord_6491256) baseStart_6491256 baseEnd_6491256 := by
    simpa [prefixWord, tailWord_6491256, baseEnd_6491256] using wordTrace_append hprefix tailTrace_6491256
  have hstable : (prefixWord ++ tailWord_6491256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491256).length < 2 ^ (prefixWord ++ tailWord_6491256).sum := by decide
  have hdescent : baseEnd_6491256 < baseStart_6491256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491303 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_6491303 : Nat := 118140960795 + 6491303 * 2 ^ 59
def prefixEnd_6491303 : Nat := 4983230072969 + 3 ^ 40 * 6491303 * 2
def baseEnd_6491303 : Nat := 3333158512972521480859547

theorem tailTrace_6491303 : CollatzResearch.WordTrace tailWord_6491303 prefixEnd_6491303 3333158512972521480859547 := by
  unfold tailWord_6491303
  simp only [CollatzResearch.WordTrace]
  refine ⟨236757270802125332135262563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157838180534750221423508375 236757270802125332135262563)
  ·
    refine ⟨355135906203187998202893845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236757270802125332135262563 355135906203187998202893845)
    ·
      refine ⟨16646995603274437415760649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 355135906203187998202893845 16646995603274437415760649)
      ·
        refine ⟨12485246702455828061820487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16646995603274437415760649 12485246702455828061820487)
        ·
          refine ⟨18727870053683742092730731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12485246702455828061820487 18727870053683742092730731)
          ·
            refine ⟨28091805080525613139096097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18727870053683742092730731 28091805080525613139096097)
            ·
              refine ⟨21068853810394209854322073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28091805080525613139096097 21068853810394209854322073)
              ·
                refine ⟨15801640357795657390741555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21068853810394209854322073 15801640357795657390741555)
                ·
                  refine ⟨23702460536693486086112333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15801640357795657390741555 23702460536693486086112333)
                  ·
                    refine ⟨8888422701260057282292125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23702460536693486086112333 8888422701260057282292125)
                    ·
                      refine ⟨3333158512972521480859547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8888422701260057282292125 3333158512972521480859547)
                      ·
                        rfl

theorem cell23_6491303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_6491303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491303 prefixEnd_6491303 := by exact prefixLift 6491303
  have htrace : WordTrace (prefixWord ++ tailWord_6491303) baseStart_6491303 baseEnd_6491303 := by
    simpa [prefixWord, tailWord_6491303, baseEnd_6491303] using wordTrace_append hprefix tailTrace_6491303
  have hstable : (prefixWord ++ tailWord_6491303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491303).length < 2 ^ (prefixWord ++ tailWord_6491303).sum := by decide
  have hdescent : baseEnd_6491303 < baseStart_6491303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491319 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 4, 6]
def baseStart_6491319 : Nat := 118140960795 + 6491319 * 2 ^ 59
def prefixEnd_6491319 : Nat := 4983230072969 + 3 ^ 40 * 6491319 * 2
def baseEnd_6491319 : Nat := 1111055576220997806086491

theorem tailTrace_6491319 : CollatzResearch.WordTrace tailWord_6491319 prefixEnd_6491319 1111055576220997806086491 := by
  unfold tailWord_6491319
  simp only [CollatzResearch.WordTrace]
  refine ⟨236757854370067366867845011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157838569580044911245230007 236757854370067366867845011)
  ·
    refine ⟨355136781555101050301767517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236757854370067366867845011 355136781555101050301767517)
    ·
      refine ⟨133176293083162893863162819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355136781555101050301767517 133176293083162893863162819)
      ·
        refine ⟨199764439624744340794744229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133176293083162893863162819 199764439624744340794744229)
        ·
          refine ⟨37455832429639563899014543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199764439624744340794744229 37455832429639563899014543)
          ·
            refine ⟨56183748644459345848521815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37455832429639563899014543 56183748644459345848521815)
            ·
              refine ⟨84275622966689018772782723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56183748644459345848521815 84275622966689018772782723)
              ·
                refine ⟨126413434450033528159174085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84275622966689018772782723 126413434450033528159174085)
                ·
                  refine ⟨23702518959381286529845141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126413434450033528159174085 23702518959381286529845141)
                  ·
                    refine ⟨1111055576220997806086491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23702518959381286529845141 1111055576220997806086491)
                    ·
                      rfl

theorem cell23_6491319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 6].length) (baseStart_6491319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491319 prefixEnd_6491319 := by exact prefixLift 6491319
  have htrace : WordTrace (prefixWord ++ tailWord_6491319) baseStart_6491319 baseEnd_6491319 := by
    simpa [prefixWord, tailWord_6491319, baseEnd_6491319] using wordTrace_append hprefix tailTrace_6491319
  have hstable : (prefixWord ++ tailWord_6491319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491319).length < 2 ^ (prefixWord ++ tailWord_6491319).sum := by decide
  have hdescent : baseEnd_6491319 < baseStart_6491319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491334 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4]
def baseStart_6491334 : Nat := 118140960795 + 6491334 * 2 ^ 59
def prefixEnd_6491334 : Nat := 4983230072969 + 3 ^ 40 * 6491334 * 2
def baseEnd_6491334 : Nat := 3333174430872810859571905

theorem tailTrace_6491334 : CollatzResearch.WordTrace tailWord_6491334 prefixEnd_6491334 3333174430872810859571905 := by
  unfold tailWord_6491334
  simp only [CollatzResearch.WordTrace]
  refine ⟨7398700045781657013426283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 157838934310008682953094037 7398700045781657013426283)
  ·
    refine ⟨11098050068672485520139425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7398700045781657013426283 11098050068672485520139425)
    ·
      refine ⟨8323537551504364140104569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11098050068672485520139425 8323537551504364140104569)
      ·
        refine ⟨6242653163628273105078427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8323537551504364140104569 6242653163628273105078427)
        ·
          refine ⟨9363979745442409657617641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6242653163628273105078427 9363979745442409657617641)
          ·
            refine ⟨7022984809081807243213231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9363979745442409657617641 7022984809081807243213231)
            ·
              refine ⟨10534477213622710864819847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7022984809081807243213231 10534477213622710864819847)
              ·
                refine ⟨15801715820434066297229771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10534477213622710864819847 15801715820434066297229771)
                ·
                  refine ⟨23702573730651099445844657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15801715820434066297229771 23702573730651099445844657)
                  ·
                    refine ⟨17776930297988324584383493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23702573730651099445844657 17776930297988324584383493)
                    ·
                      refine ⟨3333174430872810859571905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17776930297988324584383493 3333174430872810859571905)
                      ·
                        rfl

theorem cell23_6491334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_6491334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491334 prefixEnd_6491334 := by exact prefixLift 6491334
  have htrace : WordTrace (prefixWord ++ tailWord_6491334) baseStart_6491334 baseEnd_6491334 := by
    simpa [prefixWord, tailWord_6491334, baseEnd_6491334] using wordTrace_append hprefix tailTrace_6491334
  have hstable : (prefixWord ++ tailWord_6491334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491334).length < 2 ^ (prefixWord ++ tailWord_6491334).sum := by decide
  have hdescent : baseEnd_6491334 < baseStart_6491334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491339 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 4]
def baseStart_6491339 : Nat := 118140960795 + 6491339 * 2 ^ 59
def prefixEnd_6491339 : Nat := 4983230072969 + 3 ^ 40 * 6491339 * 2
def baseEnd_6491339 : Nat := 3333176998276083340009381

theorem tailTrace_6491339 : CollatzResearch.WordTrace tailWord_6491339 prefixEnd_6491339 3333176998276083340009381 := by
  unfold tailWord_6491339
  simp only [CollatzResearch.WordTrace]
  refine ⟨236758583829994910283573071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157839055886663273522382047 236758583829994910283573071)
  ·
    refine ⟨355137875744992365425359607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236758583829994910283573071 355137875744992365425359607)
    ·
      refine ⟨532706813617488548138039411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355137875744992365425359607 532706813617488548138039411)
      ·
        refine ⟨799060220426232822207059117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532706813617488548138039411 799060220426232822207059117)
        ·
          refine ⟨299647582659837308327647169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 799060220426232822207059117 299647582659837308327647169)
          ·
            refine ⟨224735686994877981245735377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299647582659837308327647169 224735686994877981245735377)
            ·
              refine ⟨168551765246158485934301533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224735686994877981245735377 168551765246158485934301533)
              ·
                refine ⟨63206911967309432225363075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168551765246158485934301533 63206911967309432225363075)
                ·
                  refine ⟨94810367950964148338044613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63206911967309432225363075 94810367950964148338044613)
                  ·
                    refine ⟨17776943990805777813383365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94810367950964148338044613 17776943990805777813383365)
                    ·
                      refine ⟨3333176998276083340009381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17776943990805777813383365 3333176998276083340009381)
                      ·
                        rfl

theorem cell23_6491339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 4].length) (baseStart_6491339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491339 prefixEnd_6491339 := by exact prefixLift 6491339
  have htrace : WordTrace (prefixWord ++ tailWord_6491339) baseStart_6491339 baseEnd_6491339 := by
    simpa [prefixWord, tailWord_6491339, baseEnd_6491339] using wordTrace_append hprefix tailTrace_6491339
  have hstable : (prefixWord ++ tailWord_6491339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491339).length < 2 ^ (prefixWord ++ tailWord_6491339).sum := by decide
  have hdescent : baseEnd_6491339 < baseStart_6491339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491346 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_6491346 : Nat := 118140960795 + 6491346 * 2 ^ 59
def prefixEnd_6491346 : Nat := 4983230072969 + 3 ^ 40 * 6491346 * 2
def baseEnd_6491346 : Nat := 3333180592640664812621849

theorem tailTrace_6491346 : CollatzResearch.WordTrace tailWord_6491346 prefixEnd_6491346 3333180592640664812621849 := by
  unfold tailWord_6491346
  simp only [CollatzResearch.WordTrace]
  refine ⟨59189709785242387619769473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157839226093979700319385261 59189709785242387619769473)
  ·
    refine ⟨44392282338931790714827105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59189709785242387619769473 44392282338931790714827105)
    ·
      refine ⟨33294211754198843036120329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44392282338931790714827105 33294211754198843036120329)
      ·
        refine ⟨24970658815649132277090247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33294211754198843036120329 24970658815649132277090247)
        ·
          refine ⟨37455988223473698415635371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24970658815649132277090247 37455988223473698415635371)
          ·
            refine ⟨56183982335210547623453057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37455988223473698415635371 56183982335210547623453057)
            ·
              refine ⟨42137986751407910717589793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56183982335210547623453057 42137986751407910717589793)
              ·
                refine ⟨31603490063555933038192345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42137986751407910717589793 31603490063555933038192345)
                ·
                  refine ⟨23702617547666949778644259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31603490063555933038192345 23702617547666949778644259)
                  ·
                    refine ⟨35553926321500424667966389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23702617547666949778644259 35553926321500424667966389)
                    ·
                      refine ⟨3333180592640664812621849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35553926321500424667966389 3333180592640664812621849)
                      ·
                        rfl

theorem cell23_6491346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_6491346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491346 prefixEnd_6491346 := by exact prefixLift 6491346
  have htrace : WordTrace (prefixWord ++ tailWord_6491346) baseStart_6491346 baseEnd_6491346 := by
    simpa [prefixWord, tailWord_6491346, baseEnd_6491346] using wordTrace_append hprefix tailTrace_6491346
  have hstable : (prefixWord ++ tailWord_6491346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491346).length < 2 ^ (prefixWord ++ tailWord_6491346).sum := by decide
  have hdescent : baseEnd_6491346 < baseStart_6491346 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491394 : List Nat := [3, 4, 1, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_6491394 : Nat := 118140960795 + 6491394 * 2 ^ 59
def prefixEnd_6491394 : Nat := 4983230072969 + 3 ^ 40 * 6491394 * 2
def baseEnd_6491394 : Nat := 3333205239712080624821629

theorem tailTrace_6491394 : CollatzResearch.WordTrace tailWord_6491394 prefixEnd_6491394 3333205239712080624821629 := by
  unfold tailWord_6491394
  simp only [CollatzResearch.WordTrace]
  refine ⟨59190147461198913669206309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157840393229863769784550157 59190147461198913669206309)
  ·
    refine ⟨11098152648974796312976183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59190147461198913669206309 11098152648974796312976183)
    ·
      refine ⟨16647228973462194469464275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11098152648974796312976183 16647228973462194469464275)
      ·
        refine ⟨24970843460193291704196413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16647228973462194469464275 24970843460193291704196413)
        ·
          refine ⟨9364066297572484389073655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24970843460193291704196413 9364066297572484389073655)
          ·
            refine ⟨14046099446358726583610483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9364066297572484389073655 14046099446358726583610483)
            ·
              refine ⟨21069149169538089875415725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14046099446358726583610483 21069149169538089875415725)
              ·
                refine ⟨7900930938576783703280897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21069149169538089875415725 7900930938576783703280897)
                ·
                  refine ⟨5925698203932587777460673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7900930938576783703280897 5925698203932587777460673)
                  ·
                    refine ⟨4444273652949440833095505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5925698203932587777460673 4444273652949440833095505)
                    ·
                      refine ⟨3333205239712080624821629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4444273652949440833095505 3333205239712080624821629)
                      ·
                        rfl

theorem cell23_6491394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_6491394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491394 prefixEnd_6491394 := by exact prefixLift 6491394
  have htrace : WordTrace (prefixWord ++ tailWord_6491394) baseStart_6491394 baseEnd_6491394 := by
    simpa [prefixWord, tailWord_6491394, baseEnd_6491394] using wordTrace_append hprefix tailTrace_6491394
  have hstable : (prefixWord ++ tailWord_6491394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491394).length < 2 ^ (prefixWord ++ tailWord_6491394).sum := by decide
  have hdescent : baseEnd_6491394 < baseStart_6491394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491436 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 3]
def baseStart_6491436 : Nat := 118140960795 + 6491436 * 2 ^ 59
def prefixEnd_6491436 : Nat := 4983230072969 + 3 ^ 40 * 6491436 * 2
def baseEnd_6491436 : Nat := 3333226805899569460496435

theorem tailTrace_6491436 : CollatzResearch.WordTrace tailWord_6491436 prefixEnd_6491436 3333226805899569460496435 := by
  unfold tailWord_6491436
  simp only [CollatzResearch.WordTrace]
  refine ⟨118381060855321747924927081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157841414473762330566569441 118381060855321747924927081)
  ·
    refine ⟨88785795641491310943695311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118381060855321747924927081 88785795641491310943695311)
    ·
      refine ⟨133178693462236966415542967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88785795641491310943695311 133178693462236966415542967)
      ·
        refine ⟨199768040193355449623314451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133178693462236966415542967 199768040193355449623314451)
        ·
          refine ⟨299652060290033174434971677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199768040193355449623314451 299652060290033174434971677)
          ·
            refine ⟨112369522608762440413114379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299652060290033174434971677 112369522608762440413114379)
            ·
              refine ⟨168554283913143660619671569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112369522608762440413114379 168554283913143660619671569)
              ·
                refine ⟨126415712934857745464753677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168554283913143660619671569 126415712934857745464753677)
                ·
                  refine ⟨47405892350571654549282629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126415712934857745464753677 47405892350571654549282629)
                  ·
                    refine ⟨8888604815732185227990493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47405892350571654549282629 8888604815732185227990493)
                    ·
                      refine ⟨3333226805899569460496435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8888604815732185227990493 3333226805899569460496435)
                      ·
                        rfl

theorem cell23_6491436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_6491436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491436 prefixEnd_6491436 := by exact prefixLift 6491436
  have htrace : WordTrace (prefixWord ++ tailWord_6491436) baseStart_6491436 baseEnd_6491436 := by
    simpa [prefixWord, tailWord_6491436, baseEnd_6491436] using wordTrace_append hprefix tailTrace_6491436
  have hstable : (prefixWord ++ tailWord_6491436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491436).length < 2 ^ (prefixWord ++ tailWord_6491436).sum := by decide
  have hdescent : baseEnd_6491436 < baseStart_6491436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491456 : List Nat := [2, 1, 1, 2, 2, 1, 3, 5, 6]
def baseStart_6491456 : Nat := 118140960795 + 6491456 * 2 ^ 59
def prefixEnd_6491456 : Nat := 4983230072969 + 3 ^ 40 * 6491456 * 2
def baseEnd_6491456 : Nat := 370359675056962153582927

theorem tailTrace_6491456 : CollatzResearch.WordTrace tailWord_6491456 prefixEnd_6491456 370359675056962153582927 := by
  unfold tailWord_6491456
  simp only [CollatzResearch.WordTrace]
  refine ⟨118381425585285519632791111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157841900780380692843721481 118381425585285519632791111)
  ·
    refine ⟨177572138377928279449186667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118381425585285519632791111 177572138377928279449186667)
    ·
      refine ⟨266358207566892419173780001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177572138377928279449186667 266358207566892419173780001)
      ·
        refine ⟨199768655675169314380335001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266358207566892419173780001 199768655675169314380335001)
        ·
          refine ⟨149826491756376985785251251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199768655675169314380335001 149826491756376985785251251)
          ·
            refine ⟨224739737634565478677876877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149826491756376985785251251 224739737634565478677876877)
            ·
              refine ⟨84277401612962054504203829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224739737634565478677876877 84277401612962054504203829)
              ·
                refine ⟨7901006401215192609769109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84277401612962054504203829 7901006401215192609769109)
                ·
                  refine ⟨370359675056962153582927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7901006401215192609769109 370359675056962153582927)
                  ·
                    rfl

theorem cell23_6491456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 6].length) (baseStart_6491456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491456 prefixEnd_6491456 := by exact prefixLift 6491456
  have htrace : WordTrace (prefixWord ++ tailWord_6491456) baseStart_6491456 baseEnd_6491456 := by
    simpa [prefixWord, tailWord_6491456, baseEnd_6491456] using wordTrace_append hprefix tailTrace_6491456
  have hstable : (prefixWord ++ tailWord_6491456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491456).length < 2 ^ (prefixWord ++ tailWord_6491456).sum := by decide
  have hdescent : baseEnd_6491456 < baseStart_6491456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491460 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 5, 4]
def baseStart_6491460 : Nat := 118140960795 + 6491460 * 2 ^ 59
def prefixEnd_6491460 : Nat := 4983230072969 + 3 ^ 40 * 6491460 * 2
def baseEnd_6491460 : Nat := 1111079709811759122198775

theorem tailTrace_6491460 : CollatzResearch.WordTrace tailWord_6491460 prefixEnd_6491460 1111079709811759122198775 := by
  unfold tailWord_6491460
  simp only [CollatzResearch.WordTrace]
  refine ⟨118381498531278273974363917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157841998041704365299151889 118381498531278273974363917)
  ·
    refine ⟨44393061949229352740386469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118381498531278273974363917 44393061949229352740386469)
    ·
      refine ⟨8323699115480503638822463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44393061949229352740386469 8323699115480503638822463)
      ·
        refine ⟨12485548673220755458233695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8323699115480503638822463 12485548673220755458233695)
        ·
          refine ⟨18728323009831133187350543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12485548673220755458233695 18728323009831133187350543)
          ·
            refine ⟨28092484514746699781025815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18728323009831133187350543 28092484514746699781025815)
            ·
              refine ⟨42138726772120049671538723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28092484514746699781025815 42138726772120049671538723)
              ·
                refine ⟨63208090158180074507308085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42138726772120049671538723 63208090158180074507308085)
                ·
                  refine ⟨5925758452329381985060133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63208090158180074507308085 5925758452329381985060133)
                  ·
                    refine ⟨1111079709811759122198775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5925758452329381985060133 1111079709811759122198775)
                    ·
                      rfl

theorem cell23_6491460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_6491460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491460 prefixEnd_6491460 := by exact prefixLift 6491460
  have htrace : WordTrace (prefixWord ++ tailWord_6491460) baseStart_6491460 baseEnd_6491460 := by
    simpa [prefixWord, tailWord_6491460, baseEnd_6491460] using wordTrace_append hprefix tailTrace_6491460
  have hstable : (prefixWord ++ tailWord_6491460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491460).length < 2 ^ (prefixWord ++ tailWord_6491460).sum := by decide
  have hdescent : baseEnd_6491460 < baseStart_6491460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491477 : List Nat := [1, 3, 2, 2, 3, 2, 2, 3, 1, 4]
def baseStart_6491477 : Nat := 118140960795 + 6491477 * 2 ^ 59
def prefixEnd_6491477 : Nat := 4983230072969 + 3 ^ 40 * 6491477 * 2
def baseEnd_6491477 : Nat := 1111082619535467933361249

theorem tailTrace_6491477 : CollatzResearch.WordTrace tailWord_6491477 prefixEnd_6491477 1111082619535467933361249 := by
  unfold tailWord_6491477
  simp only [CollatzResearch.WordTrace]
  refine ⟨236763617103494959852096685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157842411402329973234731123 236763617103494959852096685)
  ·
    refine ⟨88786356413810609944536257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236763617103494959852096685 88786356413810609944536257)
    ·
      refine ⟨66589767310357957458402193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88786356413810609944536257 66589767310357957458402193)
      ·
        refine ⟨49942325482768468093801645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66589767310357957458402193 49942325482768468093801645)
        ·
          refine ⟨18728372056038175535175617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49942325482768468093801645 18728372056038175535175617)
          ·
            refine ⟨14046279042028631651381713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18728372056038175535175617 14046279042028631651381713)
            ·
              refine ⟨10534709281521473738536285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14046279042028631651381713 10534709281521473738536285)
              ·
                refine ⟨3950515980570552651951107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10534709281521473738536285 3950515980570552651951107)
                ·
                  refine ⟨5925773970855828977926661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3950515980570552651951107 5925773970855828977926661)
                  ·
                    refine ⟨1111082619535467933361249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5925773970855828977926661 1111082619535467933361249)
                    ·
                      rfl

theorem cell23_6491477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_6491477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491477 prefixEnd_6491477 := by exact prefixLift 6491477
  have htrace : WordTrace (prefixWord ++ tailWord_6491477) baseStart_6491477 baseEnd_6491477 := by
    simpa [prefixWord, tailWord_6491477, baseEnd_6491477] using wordTrace_append hprefix tailTrace_6491477
  have hstable : (prefixWord ++ tailWord_6491477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491477).length < 2 ^ (prefixWord ++ tailWord_6491477).sum := by decide
  have hdescent : baseEnd_6491477 < baseStart_6491477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491500 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 3]
def baseStart_6491500 : Nat := 118140960795 + 6491500 * 2 ^ 59
def prefixEnd_6491500 : Nat := 4983230072969 + 3 ^ 40 * 6491500 * 2
def baseEnd_6491500 : Nat := 3333259668661457210096141

theorem tailTrace_6491500 : CollatzResearch.WordTrace tailWord_6491500 prefixEnd_6491500 3333259668661457210096141 := by
  unfold tailWord_6491500
  simp only [CollatzResearch.WordTrace]
  refine ⟨118382227991205817390091977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157842970654941089853455969 118382227991205817390091977)
  ·
    refine ⟨88786670993404363042568983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118382227991205817390091977 88786670993404363042568983)
    ·
      refine ⟨133180006490106544563853475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88786670993404363042568983 133180006490106544563853475)
      ·
        refine ⟨199770009735159816845780213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133180006490106544563853475 199770009735159816845780213)
        ·
          refine ⟨18728438412671232829291895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 199770009735159816845780213 18728438412671232829291895)
          ·
            refine ⟨28092657619006849243937843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18728438412671232829291895 28092657619006849243937843)
            ·
              refine ⟨42138986428510273865906765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28092657619006849243937843 42138986428510273865906765)
              ·
                refine ⟨15802119910691352699715037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42138986428510273865906765 15802119910691352699715037)
                ·
                  refine ⟨5925794966509257262393139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15802119910691352699715037 5925794966509257262393139)
                  ·
                    refine ⟨8888692449763885893589709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5925794966509257262393139 8888692449763885893589709)
                    ·
                      refine ⟨3333259668661457210096141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8888692449763885893589709 3333259668661457210096141)
                      ·
                        rfl

theorem cell23_6491500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 3].length) (baseStart_6491500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491500 prefixEnd_6491500 := by exact prefixLift 6491500
  have htrace : WordTrace (prefixWord ++ tailWord_6491500) baseStart_6491500 baseEnd_6491500 := by
    simpa [prefixWord, tailWord_6491500, baseEnd_6491500] using wordTrace_append hprefix tailTrace_6491500
  have hstable : (prefixWord ++ tailWord_6491500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491500).length < 2 ^ (prefixWord ++ tailWord_6491500).sum := by decide
  have hdescent : baseEnd_6491500 < baseStart_6491500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491543 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 3]
def baseStart_6491543 : Nat := 118140960795 + 6491543 * 2 ^ 59
def prefixEnd_6491543 : Nat := 4983230072969 + 3 ^ 40 * 6491543 * 2
def baseEnd_6491543 : Nat := 3333281748329600541858443

theorem tailTrace_6491543 : CollatzResearch.WordTrace tailWord_6491543 prefixEnd_6491543 3333281748329600541858443 := by
  unfold tailWord_6491543
  simp only [CollatzResearch.WordTrace]
  refine ⟨236766024321255853123999283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157844016214170568749332855 236766024321255853123999283)
  ·
    refine ⟨355149036481883779685998925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236766024321255853123999283 355149036481883779685998925)
    ·
      refine ⟨133180888680706417382249597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355149036481883779685998925 133180888680706417382249597)
      ·
        refine ⟨49942833255264906518343599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133180888680706417382249597 49942833255264906518343599)
        ·
          refine ⟨74914249882897359777515399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49942833255264906518343599 74914249882897359777515399)
          ·
            refine ⟨112371374824346039666273099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74914249882897359777515399 112371374824346039666273099)
            ·
              refine ⟨168557062236519059499409649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112371374824346039666273099 168557062236519059499409649)
              ·
                refine ⟨126417796677389294624557237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168557062236519059499409649 126417796677389294624557237)
                ·
                  refine ⟨11851668438505246371052241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126417796677389294624557237 11851668438505246371052241)
                  ·
                    refine ⟨8888751328878934778289181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11851668438505246371052241 8888751328878934778289181)
                    ·
                      refine ⟨3333281748329600541858443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8888751328878934778289181 3333281748329600541858443)
                      ·
                        rfl

theorem cell23_6491543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_6491543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491543 prefixEnd_6491543 := by exact prefixLift 6491543
  have htrace : WordTrace (prefixWord ++ tailWord_6491543) baseStart_6491543 baseEnd_6491543 := by
    simpa [prefixWord, tailWord_6491543, baseEnd_6491543] using wordTrace_append hprefix tailTrace_6491543
  have hstable : (prefixWord ++ tailWord_6491543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491543).length < 2 ^ (prefixWord ++ tailWord_6491543).sum := by decide
  have hdescent : baseEnd_6491543 < baseStart_6491543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491623 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 1, 8]
def baseStart_6491623 : Nat := 118140960795 + 6491623 * 2 ^ 59
def prefixEnd_6491623 : Nat := 4983230072969 + 3 ^ 40 * 6491623 * 2
def baseEnd_6491623 : Nat := 1111107608927320076286025

theorem tailTrace_6491623 : CollatzResearch.WordTrace tailWord_6491623 prefixEnd_6491623 1111107608927320076286025 := by
  unfold tailWord_6491623
  simp only [CollatzResearch.WordTrace]
  refine ⟨236768942160966026786911523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157845961440644017857941015 236768942160966026786911523)
  ·
    refine ⟨355153413241449040180367285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236768942160966026786911523 355153413241449040180367285)
    ·
      refine ⟨33295632491385847516909433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 355153413241449040180367285 33295632491385847516909433)
      ·
        refine ⟨24971724368539385637682075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33295632491385847516909433 24971724368539385637682075)
        ·
          refine ⟨37457586552809078456523113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24971724368539385637682075 37457586552809078456523113)
          ·
            refine ⟨28093189914606808842392335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37457586552809078456523113 28093189914606808842392335)
            ·
              refine ⟨42139784871910213263588503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28093189914606808842392335 42139784871910213263588503)
              ·
                refine ⟨63209677307865319895382755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42139784871910213263588503 63209677307865319895382755)
                ·
                  refine ⟨94814515961797979843074133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63209677307865319895382755 94814515961797979843074133)
                  ·
                    refine ⟨1111107608927320076286025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94814515961797979843074133 1111107608927320076286025)
                    ·
                      rfl

theorem cell23_6491623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_6491623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491623 prefixEnd_6491623 := by exact prefixLift 6491623
  have htrace : WordTrace (prefixWord ++ tailWord_6491623) baseStart_6491623 baseEnd_6491623 := by
    simpa [prefixWord, tailWord_6491623, baseEnd_6491623] using wordTrace_append hprefix tailTrace_6491623
  have hstable : (prefixWord ++ tailWord_6491623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491623).length < 2 ^ (prefixWord ++ tailWord_6491623).sum := by decide
  have hdescent : baseEnd_6491623 < baseStart_6491623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491681 : List Nat := [1, 2, 3, 2, 2, 3, 3, 1, 2, 2, 2]
def baseStart_6491681 : Nat := 118140960795 + 6491681 * 2 ^ 59
def prefixEnd_6491681 : Nat := 4983230072969 + 3 ^ 40 * 6491681 * 2
def baseEnd_6491681 : Nat := 3333352608659921001932809

theorem tailTrace_6491681 : CollatzResearch.WordTrace tailWord_6491681 prefixEnd_6491681 3333352608659921001932809 := by
  unfold tailWord_6491681
  simp only [CollatzResearch.WordTrace]
  refine ⟨236771057594755902692522897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157847371729837268461681931 236771057594755902692522897)
  ·
    refine ⟨177578293196066927019392173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236771057594755902692522897 177578293196066927019392173)
    ·
      refine ⟨66591859948525097632272065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177578293196066927019392173 66591859948525097632272065)
      ·
        refine ⟨49943894961393823224204049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66591859948525097632272065 49943894961393823224204049)
        ·
          refine ⟨37457921221045367418153037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49943894961393823224204049 37457921221045367418153037)
          ·
            refine ⟨14046720457892012781807389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37457921221045367418153037 14046720457892012781807389)
            ·
              refine ⟨5267520171709504793177771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14046720457892012781807389 5267520171709504793177771)
              ·
                refine ⟨7901280257564257189766657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5267520171709504793177771 7901280257564257189766657)
                ·
                  refine ⟨5925960193173192892324993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7901280257564257189766657 5925960193173192892324993)
                  ·
                    refine ⟨4444470144879894669243745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5925960193173192892324993 4444470144879894669243745)
                    ·
                      refine ⟨3333352608659921001932809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4444470144879894669243745 3333352608659921001932809)
                      ·
                        rfl

theorem cell23_6491681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 2, 2, 2].length) (baseStart_6491681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491681 prefixEnd_6491681 := by exact prefixLift 6491681
  have htrace : WordTrace (prefixWord ++ tailWord_6491681) baseStart_6491681 baseEnd_6491681 := by
    simpa [prefixWord, tailWord_6491681, baseEnd_6491681] using wordTrace_append hprefix tailTrace_6491681
  have hstable : (prefixWord ++ tailWord_6491681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491681).length < 2 ^ (prefixWord ++ tailWord_6491681).sum := by decide
  have hdescent : baseEnd_6491681 < baseStart_6491681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491777 : List Nat := [1, 2, 4, 2, 1, 3, 2, 2, 6]
def baseStart_6491777 : Nat := 118140960795 + 6491777 * 2 ^ 59
def prefixEnd_6491777 : Nat := 4983230072969 + 3 ^ 40 * 6491777 * 2
def baseEnd_6491777 : Nat := 370377989200305847370263

theorem tailTrace_6491777 : CollatzResearch.WordTrace tailWord_6491777 prefixEnd_6491777 370377989200305847370263 := by
  unfold tailWord_6491777
  simp only [CollatzResearch.WordTrace]
  refine ⟨236774559002408111088017585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157849706001605407392011723 236774559002408111088017585)
  ·
    refine ⟨177580919251806083316013189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236774559002408111088017585 177580919251806083316013189)
    ·
      refine ⟨33296422359713640621752473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 177580919251806083316013189 33296422359713640621752473)
      ·
        refine ⟨24972316769785230466314355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33296422359713640621752473 24972316769785230466314355)
        ·
          refine ⟨37458475154677845699471533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24972316769785230466314355 37458475154677845699471533)
          ·
            refine ⟨14046928183004192137301825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37458475154677845699471533 14046928183004192137301825)
            ·
              refine ⟨10535196137253144102976369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14046928183004192137301825 10535196137253144102976369)
              ·
                refine ⟨7901397102939858077232277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10535196137253144102976369 7901397102939858077232277)
                ·
                  refine ⟨370377989200305847370263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7901397102939858077232277 370377989200305847370263)
                  ·
                    rfl

theorem cell23_6491777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 6].length) (baseStart_6491777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491777 prefixEnd_6491777 := by exact prefixLift 6491777
  have htrace : WordTrace (prefixWord ++ tailWord_6491777) baseStart_6491777 baseEnd_6491777 := by
    simpa [prefixWord, tailWord_6491777, baseEnd_6491777] using wordTrace_append hprefix tailTrace_6491777
  have hstable : (prefixWord ++ tailWord_6491777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491777).length < 2 ^ (prefixWord ++ tailWord_6491777).sum := by decide
  have hdescent : baseEnd_6491777 < baseStart_6491777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491787 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 3, 1, 3]
def baseStart_6491787 : Nat := 118140960795 + 6491787 * 2 ^ 59
def prefixEnd_6491787 : Nat := 4983230072969 + 3 ^ 40 * 6491787 * 2
def baseEnd_6491787 : Nat := 3333407037609297587207321

theorem tailTrace_6491787 : CollatzResearch.WordTrace tailWord_6491787 prefixEnd_6491787 3333407037609297587207321 := by
  unfold tailWord_6491787
  simp only [CollatzResearch.WordTrace]
  refine ⟨236774923732371882795881615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157849949154914588530587743 236774923732371882795881615)
  ·
    refine ⟨355162385598557824193822423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236774923732371882795881615 355162385598557824193822423)
    ·
      refine ⟨532743578397836736290733635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355162385598557824193822423 532743578397836736290733635)
      ·
        refine ⟨799115367596755104436100453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532743578397836736290733635 799115367596755104436100453)
        ·
          refine ⟨149834131424391582081768835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 799115367596755104436100453 149834131424391582081768835)
          ·
            refine ⟨224751197136587373122653253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149834131424391582081768835 224751197136587373122653253)
            ·
              refine ⟨42140849463110132460497485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224751197136587373122653253 42140849463110132460497485)
              ·
                refine ⟨15802818548666299672686557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42140849463110132460497485 15802818548666299672686557)
                ·
                  refine ⟨5926056955749862377257459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15802818548666299672686557 5926056955749862377257459)
                  ·
                    refine ⟨8889085433624793565886189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5926056955749862377257459 8889085433624793565886189)
                    ·
                      refine ⟨3333407037609297587207321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8889085433624793565886189 3333407037609297587207321)
                      ·
                        rfl

theorem cell23_6491787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 1, 3].length) (baseStart_6491787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491787 prefixEnd_6491787 := by exact prefixLift 6491787
  have htrace : WordTrace (prefixWord ++ tailWord_6491787) baseStart_6491787 baseEnd_6491787 := by
    simpa [prefixWord, tailWord_6491787, baseEnd_6491787] using wordTrace_append hprefix tailTrace_6491787
  have hstable : (prefixWord ++ tailWord_6491787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491787).length < 2 ^ (prefixWord ++ tailWord_6491787).sum := by decide
  have hdescent : baseEnd_6491787 < baseStart_6491787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491797 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 4, 3, 2]
def baseStart_6491797 : Nat := 118140960795 + 6491797 * 2 ^ 59
def prefixEnd_6491797 : Nat := 4983230072969 + 3 ^ 40 * 6491797 * 2
def baseEnd_6491797 : Nat := 3333412172415842548082275

theorem tailTrace_6491797 : CollatzResearch.WordTrace tailWord_6491797 prefixEnd_6491797 3333412172415842548082275 := by
  unfold tailWord_6491797
  simp only [CollatzResearch.WordTrace]
  refine ⟨236775288462335654503745645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157850192308223769669163763 236775288462335654503745645)
  ·
    refine ⟨88790733173375870438904617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236775288462335654503745645 88790733173375870438904617)
    ·
      refine ⟨66593049880031902829178463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88790733173375870438904617 66593049880031902829178463)
      ·
        refine ⟨99889574820047854243767695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66593049880031902829178463 99889574820047854243767695)
        ·
          refine ⟨149834362230071781365651543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99889574820047854243767695 149834362230071781365651543)
          ·
            refine ⟨224751543345107672048477315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149834362230071781365651543 224751543345107672048477315)
            ·
              refine ⟨337127315017661508072715973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224751543345107672048477315 337127315017661508072715973)
              ·
                refine ⟨63211371565811532763634245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 337127315017661508072715973 63211371565811532763634245)
                ·
                  refine ⟨11852132168589662393181421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63211371565811532763634245 11852132168589662393181421)
                  ·
                    refine ⟨4444549563221123397443033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11852132168589662393181421 4444549563221123397443033)
                    ·
                      refine ⟨3333412172415842548082275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4444549563221123397443033 3333412172415842548082275)
                      ·
                        rfl

theorem cell23_6491797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_6491797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491797 prefixEnd_6491797 := by exact prefixLift 6491797
  have htrace : WordTrace (prefixWord ++ tailWord_6491797) baseStart_6491797 baseEnd_6491797 := by
    simpa [prefixWord, tailWord_6491797, baseEnd_6491797] using wordTrace_append hprefix tailTrace_6491797
  have hstable : (prefixWord ++ tailWord_6491797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491797).length < 2 ^ (prefixWord ++ tailWord_6491797).sum := by decide
  have hdescent : baseEnd_6491797 < baseStart_6491797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491803 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 1, 12]
def baseStart_6491803 : Nat := 118140960795 + 6491803 * 2 ^ 59
def prefixEnd_6491803 : Nat := 4983230072969 + 3 ^ 40 * 6491803 * 2
def baseEnd_6491803 : Nat := 1111138417766589841535749

theorem tailTrace_6491803 : CollatzResearch.WordTrace tailWord_6491803 prefixEnd_6491803 1111138417766589841535749 := by
  unfold tailWord_6491803
  simp only [CollatzResearch.WordTrace]
  refine ⟨236775507300313917528464063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157850338200209278352309375 236775507300313917528464063)
  ·
    refine ⟨355163260950470876292696095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236775507300313917528464063 355163260950470876292696095)
    ·
      refine ⟨532744891425706314439044143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355163260950470876292696095 532744891425706314439044143)
      ·
        refine ⟨799117337138559471658566215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532744891425706314439044143 799117337138559471658566215)
        ·
          refine ⟨1198676005707839207487849323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799117337138559471658566215 1198676005707839207487849323)
          ·
            refine ⟨1798014008561758811231773985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198676005707839207487849323 1798014008561758811231773985)
            ·
              refine ⟨1348510506421319108423830489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1798014008561758811231773985 1348510506421319108423830489)
              ·
                refine ⟨1011382879815989331317872867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1348510506421319108423830489 1011382879815989331317872867)
                ·
                  refine ⟨1517074319723983996976809301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011382879815989331317872867 1517074319723983996976809301)
                  ·
                    refine ⟨1111138417766589841535749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1517074319723983996976809301 1111138417766589841535749)
                    ·
                      rfl

theorem cell23_6491803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 12].length) (baseStart_6491803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491803 prefixEnd_6491803 := by exact prefixLift 6491803
  have htrace : WordTrace (prefixWord ++ tailWord_6491803) baseStart_6491803 baseEnd_6491803 := by
    simpa [prefixWord, tailWord_6491803, baseEnd_6491803] using wordTrace_append hprefix tailTrace_6491803
  have hstable : (prefixWord ++ tailWord_6491803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491803).length < 2 ^ (prefixWord ++ tailWord_6491803).sum := by decide
  have hdescent : baseEnd_6491803 < baseStart_6491803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491827 : List Nat := [1, 1, 1, 2, 3, 3, 3, 3, 1, 1, 4]
def baseStart_6491827 : Nat := 118140960795 + 6491827 * 2 ^ 59
def prefixEnd_6491827 : Nat := 4983230072969 + 3 ^ 40 * 6491827 * 2
def baseEnd_6491827 : Nat := 3333427576835477430707137

theorem tailTrace_6491827 : CollatzResearch.WordTrace tailWord_6491827 prefixEnd_6491827 3333427576835477430707137 := by
  unfold tailWord_6491827
  simp only [CollatzResearch.WordTrace]
  refine ⟨236776382652226969627337735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157850921768151313084891823 236776382652226969627337735)
  ·
    refine ⟨355164573978340454441006603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236776382652226969627337735 355164573978340454441006603)
    ·
      refine ⟨532746860967510681661509905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355164573978340454441006603 532746860967510681661509905)
      ·
        refine ⟨399560145725633011246132429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532746860967510681661509905 399560145725633011246132429)
        ·
          refine ⟨149835054647112379217299661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399560145725633011246132429 149835054647112379217299661)
          ·
            refine ⟨56188145492667142206487373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149835054647112379217299661 56188145492667142206487373)
            ·
              refine ⟨21070554559750178327432765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56188145492667142206487373 21070554559750178327432765)
              ·
                refine ⟨7901457959906316872787287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21070554559750178327432765 7901457959906316872787287)
                ·
                  refine ⟨11852186939859475309180931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7901457959906316872787287 11852186939859475309180931)
                  ·
                    refine ⟨17778280409789212963771397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11852186939859475309180931 17778280409789212963771397)
                    ·
                      refine ⟨3333427576835477430707137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17778280409789212963771397 3333427576835477430707137)
                      ·
                        rfl

theorem cell23_6491827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 1, 4].length) (baseStart_6491827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491827 prefixEnd_6491827 := by exact prefixLift 6491827
  have htrace : WordTrace (prefixWord ++ tailWord_6491827) baseStart_6491827 baseEnd_6491827 := by
    simpa [prefixWord, tailWord_6491827, baseEnd_6491827] using wordTrace_append hprefix tailTrace_6491827
  have hstable : (prefixWord ++ tailWord_6491827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491827).length < 2 ^ (prefixWord ++ tailWord_6491827).sum := by decide
  have hdescent : baseEnd_6491827 < baseStart_6491827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491837 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 4, 4]
def baseStart_6491837 : Nat := 118140960795 + 6491837 * 2 ^ 59
def prefixEnd_6491837 : Nat := 4983230072969 + 3 ^ 40 * 6491837 * 2
def baseEnd_6491837 : Nat := 1111144237214007463860697

theorem tailTrace_6491837 : CollatzResearch.WordTrace tailWord_6491837 prefixEnd_6491837 1111144237214007463860697 := by
  unfold tailWord_6491837
  simp only [CollatzResearch.WordTrace]
  refine ⟨236776747382190741335201765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157851164921460494223467843 236776747382190741335201765)
  ·
    refine ⟨44395640134160764000350331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236776747382190741335201765 44395640134160764000350331)
    ·
      refine ⟨66593460201241146000525497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44395640134160764000350331 66593460201241146000525497)
      ·
        refine ⟨49945095150930859500394123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66593460201241146000525497 49945095150930859500394123)
        ·
          refine ⟨74917642726396289250591185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49945095150930859500394123 74917642726396289250591185)
          ·
            refine ⟨56188232044797216937943389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74917642726396289250591185 56188232044797216937943389)
            ·
              refine ⟨21070587016798956351728771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56188232044797216937943389 21070587016798956351728771)
              ·
                refine ⟨31605880525198434527593157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21070587016798956351728771 31605880525198434527593157)
                ·
                  refine ⟨5926102598474706473923717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31605880525198434527593157 5926102598474706473923717)
                  ·
                    refine ⟨1111144237214007463860697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5926102598474706473923717 1111144237214007463860697)
                    ·
                      rfl

theorem cell23_6491837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_6491837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491837 prefixEnd_6491837 := by exact prefixLift 6491837
  have htrace : WordTrace (prefixWord ++ tailWord_6491837) baseStart_6491837 baseEnd_6491837 := by
    simpa [prefixWord, tailWord_6491837, baseEnd_6491837] using wordTrace_append hprefix tailTrace_6491837
  have hstable : (prefixWord ++ tailWord_6491837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491837).length < 2 ^ (prefixWord ++ tailWord_6491837).sum := by decide
  have hdescent : baseEnd_6491837 < baseStart_6491837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491840 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 6]
def baseStart_6491840 : Nat := 118140960795 + 6491840 * 2 ^ 59
def prefixEnd_6491840 : Nat := 4983230072969 + 3 ^ 40 * 6491840 * 2
def baseEnd_6491840 : Nat := 3333434252083985879844577

theorem tailTrace_6491840 : CollatzResearch.WordTrace tailWord_6491840 prefixEnd_6491840 3333434252083985879844577 := by
  unfold tailWord_6491840
  simp only [CollatzResearch.WordTrace]
  refine ⟨118388428400589936423780487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157851237867453248565040649 118388428400589936423780487)
  ·
    refine ⟨177582642600884904635670731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118388428400589936423780487 177582642600884904635670731)
    ·
      refine ⟨266373963901327356953506097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177582642600884904635670731 266373963901327356953506097)
      ·
        refine ⟨199780472925995517715129573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266373963901327356953506097 199780472925995517715129573)
        ·
          refine ⟨37458838673624159571586795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199780472925995517715129573 37458838673624159571586795)
          ·
            refine ⟨56188258010436239357380193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37458838673624159571586795 56188258010436239357380193)
            ·
              refine ⟨42141193507827179518035145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56188258010436239357380193 42141193507827179518035145)
              ·
                refine ⟨31605895130870384638526359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42141193507827179518035145 31605895130870384638526359)
                ·
                  refine ⟨47408842696305576957789539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31605895130870384638526359 47408842696305576957789539)
                  ·
                    refine ⟨71113264044458365436684309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47408842696305576957789539 71113264044458365436684309)
                    ·
                      refine ⟨3333434252083985879844577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71113264044458365436684309 3333434252083985879844577)
                      ·
                        rfl

theorem cell23_6491840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_6491840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491840 prefixEnd_6491840 := by exact prefixLift 6491840
  have htrace : WordTrace (prefixWord ++ tailWord_6491840) baseStart_6491840 baseEnd_6491840 := by
    simpa [prefixWord, tailWord_6491840, baseEnd_6491840] using wordTrace_append hprefix tailTrace_6491840
  have hstable : (prefixWord ++ tailWord_6491840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491840).length < 2 ^ (prefixWord ++ tailWord_6491840).sum := by decide
  have hdescent : baseEnd_6491840 < baseStart_6491840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491857 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 1, 2, 4]
def baseStart_6491857 : Nat := 118140960795 + 6491857 * 2 ^ 59
def prefixEnd_6491857 : Nat := 4983230072969 + 3 ^ 40 * 6491857 * 2
def baseEnd_6491857 : Nat := 3333442981255112313331999

theorem tailTrace_6491857 : CollatzResearch.WordTrace tailWord_6491857 prefixEnd_6491857 3333442981255112313331999 := by
  unfold tailWord_6491857
  simp only [CollatzResearch.WordTrace]
  refine ⟨236777476842118284750929825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157851651228078856500619883 236777476842118284750929825)
  ·
    refine ⟨177583107631588713563197369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236777476842118284750929825 177583107631588713563197369)
    ·
      refine ⟨133187330723691535172398027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177583107631588713563197369 133187330723691535172398027)
      ·
        refine ⟨199780996085537302758597041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133187330723691535172398027 199780996085537302758597041)
        ·
          refine ⟨149835747064152977068947781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199780996085537302758597041 149835747064152977068947781)
          ·
            refine ⟨28094202574528683200427709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149835747064152977068947781 28094202574528683200427709)
            ·
              refine ⟨10535325965448256200160391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28094202574528683200427709 10535325965448256200160391)
              ·
                refine ⟨15802988948172384300240587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10535325965448256200160391 15802988948172384300240587)
                ·
                  refine ⟨23704483422258576450360881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15802988948172384300240587 23704483422258576450360881)
                  ·
                    refine ⟨17778362566693932337770661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23704483422258576450360881 17778362566693932337770661)
                    ·
                      refine ⟨3333442981255112313331999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17778362566693932337770661 3333442981255112313331999)
                      ·
                        rfl

theorem cell23_6491857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_6491857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491857 prefixEnd_6491857 := by exact prefixLift 6491857
  have htrace : WordTrace (prefixWord ++ tailWord_6491857) baseStart_6491857 baseEnd_6491857 := by
    simpa [prefixWord, tailWord_6491857, baseEnd_6491857] using wordTrace_append hprefix tailTrace_6491857
  have hstable : (prefixWord ++ tailWord_6491857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491857).length < 2 ^ (prefixWord ++ tailWord_6491857).sum := by decide
  have hdescent : baseEnd_6491857 < baseStart_6491857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491864 : List Nat := [2, 1, 2, 2, 3, 1, 4, 2, 1, 2, 3]
def baseStart_6491864 : Nat := 118140960795 + 6491864 * 2 ^ 59
def prefixEnd_6491864 : Nat := 4983230072969 + 3 ^ 40 * 6491864 * 2
def baseEnd_6491864 : Nat := 3333446575619693785944467

theorem tailTrace_6491864 : CollatzResearch.WordTrace tailWord_6491864 prefixEnd_6491864 3333446575619693785944467 := by
  unfold tailWord_6491864
  simp only [CollatzResearch.WordTrace]
  refine ⟨118388866076546462473217323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157851821435395283297623097 118388866076546462473217323)
  ·
    refine ⟨177583299114819693709825985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118388866076546462473217323 177583299114819693709825985)
    ·
      refine ⟨133187474336114770282369489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177583299114819693709825985 133187474336114770282369489)
      ·
        refine ⟨99890605752086077711777117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133187474336114770282369489 99890605752086077711777117)
        ·
          refine ⟨37458977157032279141916419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99890605752086077711777117 37458977157032279141916419)
          ·
            refine ⟨56188465735548418712874629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37458977157032279141916419 56188465735548418712874629)
            ·
              refine ⟨10535337325415328508663993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56188465735548418712874629 10535337325415328508663993)
              ·
                refine ⟨7901502994061496381497995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10535337325415328508663993 7901502994061496381497995)
                ·
                  refine ⟨11852254491092244572246993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7901502994061496381497995 11852254491092244572246993)
                  ·
                    refine ⟨8889190868319183429185245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11852254491092244572246993 8889190868319183429185245)
                    ·
                      refine ⟨3333446575619693785944467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8889190868319183429185245 3333446575619693785944467)
                      ·
                        rfl

theorem cell23_6491864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 1, 2, 3].length) (baseStart_6491864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491864 prefixEnd_6491864 := by exact prefixLift 6491864
  have htrace : WordTrace (prefixWord ++ tailWord_6491864) baseStart_6491864 baseEnd_6491864 := by
    simpa [prefixWord, tailWord_6491864, baseEnd_6491864] using wordTrace_append hprefix tailTrace_6491864
  have hstable : (prefixWord ++ tailWord_6491864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491864).length < 2 ^ (prefixWord ++ tailWord_6491864).sum := by decide
  have hdescent : baseEnd_6491864 < baseStart_6491864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491877 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 3, 3, 3]
def baseStart_6491877 : Nat := 118140960795 + 6491877 * 2 ^ 59
def prefixEnd_6491877 : Nat := 4983230072969 + 3 ^ 40 * 6491877 * 2
def baseEnd_6491877 : Nat := 3333453250868202235081907

theorem tailTrace_6491877 : CollatzResearch.WordTrace tailWord_6491877 prefixEnd_6491877 3333453250868202235081907 := by
  unfold tailWord_6491877
  simp only [CollatzResearch.WordTrace]
  refine ⟨236778206302045828166657885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157852137534697218777771923 236778206302045828166657885)
  ·
    refine ⟨88791827363267185562496707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236778206302045828166657885 88791827363267185562496707)
    ·
      refine ⟨133187741044900778343745061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88791827363267185562496707 133187741044900778343745061)
      ·
        refine ⟨24972701445918895939452199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133187741044900778343745061 24972701445918895939452199)
        ·
          refine ⟨37459052168878343909178299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24972701445918895939452199 37459052168878343909178299)
          ·
            refine ⟨56188578253317515863767449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37459052168878343909178299 56188578253317515863767449)
            ·
              refine ⟨42141433689988136897825587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56188578253317515863767449 42141433689988136897825587)
              ·
                refine ⟨63212150534982205346738381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42141433689988136897825587 63212150534982205346738381)
                ·
                  refine ⟨23704556450618327005026893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63212150534982205346738381 23704556450618327005026893)
                  ·
                    refine ⟨8889208668981872626885085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23704556450618327005026893 8889208668981872626885085)
                    ·
                      refine ⟨3333453250868202235081907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8889208668981872626885085 3333453250868202235081907)
                      ·
                        rfl

theorem cell23_6491877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_6491877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491877 prefixEnd_6491877 := by exact prefixLift 6491877
  have htrace : WordTrace (prefixWord ++ tailWord_6491877) baseStart_6491877 baseEnd_6491877 := by
    simpa [prefixWord, tailWord_6491877, baseEnd_6491877] using wordTrace_append hprefix tailTrace_6491877
  have hstable : (prefixWord ++ tailWord_6491877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491877).length < 2 ^ (prefixWord ++ tailWord_6491877).sum := by decide
  have hdescent : baseEnd_6491877 < baseStart_6491877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491937 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_6491937 : Nat := 118140960795 + 6491937 * 2 ^ 59
def prefixEnd_6491937 : Nat := 4983230072969 + 3 ^ 40 * 6491937 * 2
def baseEnd_6491937 : Nat := 3333484059707472000331631

theorem tailTrace_6491937 : CollatzResearch.WordTrace tailWord_6491937 prefixEnd_6491937 3333484059707472000331631 := by
  unfold tailWord_6491937
  simp only [CollatzResearch.WordTrace]
  refine ⟨236780394681828458413842065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157853596454552305609228043 236780394681828458413842065)
  ·
    refine ⟨177585296011371343810381549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236780394681828458413842065 177585296011371343810381549)
    ·
      refine ⟨66594486004264253928893081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177585296011371343810381549 66594486004264253928893081)
      ·
        refine ⟨49945864503198190446669811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66594486004264253928893081 49945864503198190446669811)
        ·
          refine ⟨74918796754797285670004717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49945864503198190446669811 74918796754797285670004717)
          ·
            refine ⟨28094548783048982126251769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74918796754797285670004717 28094548783048982126251769)
            ·
              refine ⟨21070911587286736594688827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28094548783048982126251769 21070911587286736594688827)
              ·
                refine ⟨31606367380930104892033241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21070911587286736594688827 31606367380930104892033241)
                ·
                  refine ⟨23704775535697578669024931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31606367380930104892033241 23704775535697578669024931)
                  ·
                    refine ⟨35557163303546368003537397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23704775535697578669024931 35557163303546368003537397)
                    ·
                      refine ⟨3333484059707472000331631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35557163303546368003537397 3333484059707472000331631)
                      ·
                        rfl

theorem cell23_6491937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_6491937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491937 prefixEnd_6491937 := by exact prefixLift 6491937
  have htrace : WordTrace (prefixWord ++ tailWord_6491937) baseStart_6491937 baseEnd_6491937 := by
    simpa [prefixWord, tailWord_6491937, baseEnd_6491937] using wordTrace_append hprefix tailTrace_6491937
  have hstable : (prefixWord ++ tailWord_6491937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491937).length < 2 ^ (prefixWord ++ tailWord_6491937).sum := by decide
  have hdescent : baseEnd_6491937 < baseStart_6491937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491938 : List Nat := [3, 3, 1, 1, 2, 1, 5, 1, 1, 3, 2]
def baseStart_6491938 : Nat := 118140960795 + 6491938 * 2 ^ 59
def prefixEnd_6491938 : Nat := 4983230072969 + 3 ^ 40 * 6491938 * 2
def baseEnd_6491938 : Nat := 3333484573188126496419127

theorem tailTrace_6491938 : CollatzResearch.WordTrace tailWord_6491938 prefixEnd_6491938 3333484573188126496419127 := by
  unfold tailWord_6491938
  simp only [CollatzResearch.WordTrace]
  refine ⟨59195107788706208896157117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157853620769883223723085645 59195107788706208896157117)
  ·
    refine ⟨22198165420764828336058919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59195107788706208896157117 22198165420764828336058919)
    ·
      refine ⟨33297248131147242504088379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22198165420764828336058919 33297248131147242504088379)
      ·
        refine ⟨49945872196720863756132569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33297248131147242504088379 49945872196720863756132569)
        ·
          refine ⟨37459404147540647817099427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49945872196720863756132569 37459404147540647817099427)
          ·
            refine ⟨56189106221310971725649141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37459404147540647817099427 56189106221310971725649141)
            ·
              refine ⟨5267728708247903599279607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56189106221310971725649141 5267728708247903599279607)
              ·
                refine ⟨7901593062371855398919411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5267728708247903599279607 7901593062371855398919411)
                ·
                  refine ⟨11852389593557783098379117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7901593062371855398919411 11852389593557783098379117)
                  ·
                    refine ⟨4444646097584168661892169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11852389593557783098379117 4444646097584168661892169)
                    ·
                      refine ⟨3333484573188126496419127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4444646097584168661892169 3333484573188126496419127)
                      ·
                        rfl

theorem cell23_6491938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_6491938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491938 prefixEnd_6491938 := by exact prefixLift 6491938
  have htrace : WordTrace (prefixWord ++ tailWord_6491938) baseStart_6491938 baseEnd_6491938 := by
    simpa [prefixWord, tailWord_6491938, baseEnd_6491938] using wordTrace_append hprefix tailTrace_6491938
  have hstable : (prefixWord ++ tailWord_6491938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491938).length < 2 ^ (prefixWord ++ tailWord_6491938).sum := by decide
  have hdescent : baseEnd_6491938 < baseStart_6491938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6491991 : List Nat := [1, 1, 3, 2, 5, 1, 2, 3, 5]
def baseStart_6491991 : Nat := 118140960795 + 6491991 * 2 ^ 59
def prefixEnd_6491991 : Nat := 4983230072969 + 3 ^ 40 * 6491991 * 2
def baseEnd_6491991 : Nat := 370390198629201643228487

theorem tailTrace_6491991 : CollatzResearch.WordTrace tailWord_6491991 prefixEnd_6491991 370390198629201643228487 := by
  unfold tailWord_6491991
  simp only [CollatzResearch.WordTrace]
  refine ⟨236782364223632825636307827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157854909482421883757538551 236782364223632825636307827)
  ·
    refine ⟨355173546335449238454461741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236782364223632825636307827 355173546335449238454461741)
    ·
      refine ⟨133190079875793464420423153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355173546335449238454461741 133190079875793464420423153)
      ·
        refine ⟨99892559906845098315317365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133190079875793464420423153 99892559906845098315317365)
        ·
          refine ⟨9364927491266727967061003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99892559906845098315317365 9364927491266727967061003)
          ·
            refine ⟨14047391236900091950591505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9364927491266727967061003 14047391236900091950591505)
            ·
              refine ⟨10535543427675068962943629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14047391236900091950591505 10535543427675068962943629)
              ·
                refine ⟨3950828785378150861103861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10535543427675068962943629 3950828785378150861103861)
                ·
                  refine ⟨370390198629201643228487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3950828785378150861103861 370390198629201643228487)
                  ·
                    rfl

theorem cell23_6491991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 2, 3, 5].length) (baseStart_6491991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6491991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6491991 prefixEnd_6491991 := by exact prefixLift 6491991
  have htrace : WordTrace (prefixWord ++ tailWord_6491991) baseStart_6491991 baseEnd_6491991 := by
    simpa [prefixWord, tailWord_6491991, baseEnd_6491991] using wordTrace_append hprefix tailTrace_6491991
  have hstable : (prefixWord ++ tailWord_6491991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6491991).length < 2 ^ (prefixWord ++ tailWord_6491991).sum := by decide
  have hdescent : baseEnd_6491991 < baseStart_6491991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6491991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492037 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 2, 4, 4]
def baseStart_6492037 : Nat := 118140960795 + 6492037 * 2 ^ 59
def prefixEnd_6492037 : Nat := 4983230072969 + 3 ^ 40 * 6492037 * 2
def baseEnd_6492037 : Nat := 3333535407772921609081171

theorem tailTrace_6492037 : CollatzResearch.WordTrace tailWord_6492037 prefixEnd_6492037 3333535407772921609081171 := by
  unfold tailWord_6492037
  simp only [CollatzResearch.WordTrace]
  refine ⟨236784041981466175492482365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157856027987644116994988243 236784041981466175492482365)
  ·
    refine ⟨88794015743049815809680887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236784041981466175492482365 88794015743049815809680887)
    ·
      refine ⟨133191023614574723714521331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88794015743049815809680887 133191023614574723714521331)
      ·
        refine ⟨199786535421862085571781997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133191023614574723714521331 199786535421862085571781997)
        ·
          refine ⟨74919950783198282089418249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199786535421862085571781997 74919950783198282089418249)
          ·
            refine ⟨56189963087398711567063687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74919950783198282089418249 56189963087398711567063687)
            ·
              refine ⟨84284944631098067350595531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56189963087398711567063687 84284944631098067350595531)
              ·
                refine ⟨126427416946647101025893297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84284944631098067350595531 126427416946647101025893297)
                ·
                  refine ⟨94820562709985325769419973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126427416946647101025893297 94820562709985325769419973)
                  ·
                    refine ⟨17778855508122248581766245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94820562709985325769419973 17778855508122248581766245)
                    ·
                      refine ⟨3333535407772921609081171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17778855508122248581766245 3333535407772921609081171)
                      ·
                        rfl

theorem cell23_6492037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_6492037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492037 prefixEnd_6492037 := by exact prefixLift 6492037
  have htrace : WordTrace (prefixWord ++ tailWord_6492037) baseStart_6492037 baseEnd_6492037 := by
    simpa [prefixWord, tailWord_6492037, baseEnd_6492037] using wordTrace_append hprefix tailTrace_6492037
  have hstable : (prefixWord ++ tailWord_6492037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492037).length < 2 ^ (prefixWord ++ tailWord_6492037).sum := by decide
  have hdescent : baseEnd_6492037 < baseStart_6492037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492044 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 2, 2, 3]
def baseStart_6492044 : Nat := 118140960795 + 6492044 * 2 ^ 59
def prefixEnd_6492044 : Nat := 4983230072969 + 3 ^ 40 * 6492044 * 2
def baseEnd_6492044 : Nat := 3333539002137503081693639

theorem tailTrace_6492044 : CollatzResearch.WordTrace tailWord_6492044 prefixEnd_6492044 3333539002137503081693639 := by
  unfold tailWord_6492044
  simp only [CollatzResearch.WordTrace]
  refine ⟨118392148646220407843993593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157856198194960543791991457 118392148646220407843993593)
  ·
    refine ⟨88794111484665305882995195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118392148646220407843993593 88794111484665305882995195)
    ·
      refine ⟨133191167226997958824492793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88794111484665305882995195 133191167226997958824492793)
      ·
        refine ⟨99893375420248469118369595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133191167226997958824492793 99893375420248469118369595)
        ·
          refine ⟨149840063130372703677554393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99893375420248469118369595 149840063130372703677554393)
          ·
            refine ⟨112380047347779527758165795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149840063130372703677554393 112380047347779527758165795)
            ·
              refine ⟨168570071021669291637248693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112380047347779527758165795 168570071021669291637248693)
              ·
                refine ⟨15803444158281496090992065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168570071021669291637248693 15803444158281496090992065)
                ·
                  refine ⟨11852583118711122068244049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15803444158281496090992065 11852583118711122068244049)
                  ·
                    refine ⟨8889437339033341551183037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11852583118711122068244049 8889437339033341551183037)
                    ·
                      refine ⟨3333539002137503081693639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8889437339033341551183037 3333539002137503081693639)
                      ·
                        rfl

theorem cell23_6492044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_6492044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492044 prefixEnd_6492044 := by exact prefixLift 6492044
  have htrace : WordTrace (prefixWord ++ tailWord_6492044) baseStart_6492044 baseEnd_6492044 := by
    simpa [prefixWord, tailWord_6492044, baseEnd_6492044] using wordTrace_append hprefix tailTrace_6492044
  have hstable : (prefixWord ++ tailWord_6492044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492044).length < 2 ^ (prefixWord ++ tailWord_6492044).sum := by decide
  have hdescent : baseEnd_6492044 < baseStart_6492044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492061 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_6492061 : Nat := 118140960795 + 6492061 * 2 ^ 59
def prefixEnd_6492061 : Nat := 4983230072969 + 3 ^ 40 * 6492061 * 2
def baseEnd_6492061 : Nat := 3333547731308629515181061

theorem tailTrace_6492061 : CollatzResearch.WordTrace tailWord_6492061 prefixEnd_6492061 3333547731308629515181061 := by
  unfold tailWord_6492061
  simp only [CollatzResearch.WordTrace]
  refine ⟨236784917333379227591356037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157856611555586151727570691 236784917333379227591356037)
  ·
    refine ⟨44397172000008605173379257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236784917333379227591356037 44397172000008605173379257)
    ·
      refine ⟨33297879000006453880034443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44397172000008605173379257 33297879000006453880034443)
      ·
        refine ⟨49946818500009680820051665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33297879000006453880034443 49946818500009680820051665)
        ·
          refine ⟨37460113875007260615038749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49946818500009680820051665 37460113875007260615038749)
          ·
            refine ⟨14047542703127722730639531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37460113875007260615038749 14047542703127722730639531)
            ·
              refine ⟨21071314054691584095959297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14047542703127722730639531 21071314054691584095959297)
              ·
                refine ⟨15803485541018688071969473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21071314054691584095959297 15803485541018688071969473)
                ·
                  refine ⟨11852614155764016053977105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15803485541018688071969473 11852614155764016053977105)
                  ·
                    refine ⟨8889460616823012040482829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11852614155764016053977105 8889460616823012040482829)
                    ·
                      refine ⟨3333547731308629515181061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8889460616823012040482829 3333547731308629515181061)
                      ·
                        rfl

theorem cell23_6492061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_6492061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492061 prefixEnd_6492061 := by exact prefixLift 6492061
  have htrace : WordTrace (prefixWord ++ tailWord_6492061) baseStart_6492061 baseEnd_6492061 := by
    simpa [prefixWord, tailWord_6492061, baseEnd_6492061] using wordTrace_append hprefix tailTrace_6492061
  have hstable : (prefixWord ++ tailWord_6492061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492061).length < 2 ^ (prefixWord ++ tailWord_6492061).sum := by decide
  have hdescent : baseEnd_6492061 < baseStart_6492061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492081 : List Nat := [1, 2, 2, 4, 2, 1, 4, 1, 6]
def baseStart_6492081 : Nat := 118140960795 + 6492081 * 2 ^ 59
def prefixEnd_6492081 : Nat := 4983230072969 + 3 ^ 40 * 6492081 * 2
def baseEnd_6492081 : Nat := 370395333435746604103441

theorem tailTrace_6492081 : CollatzResearch.WordTrace tailWord_6492081 prefixEnd_6492081 370395333435746604103441 := by
  unfold tailWord_6492081
  simp only [CollatzResearch.WordTrace]
  refine ⟨236785646793306771007084097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157857097862204514004722731 236785646793306771007084097)
  ·
    refine ⟨177589235094980078255313073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236785646793306771007084097 177589235094980078255313073)
    ·
      refine ⟨133191926321235058691484805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177589235094980078255313073 133191926321235058691484805)
      ·
        refine ⟨24973486185231573504653401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133191926321235058691484805 24973486185231573504653401)
        ·
          refine ⟨18730114638923680128490051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24973486185231573504653401 18730114638923680128490051)
          ·
            refine ⟨28095171958385520192735077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18730114638923680128490051 28095171958385520192735077)
            ·
              refine ⟨5267844742197285036137827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28095171958385520192735077 5267844742197285036137827)
              ·
                refine ⟨7901767113295927554206741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5267844742197285036137827 7901767113295927554206741)
                ·
                  refine ⟨370395333435746604103441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7901767113295927554206741 370395333435746604103441)
                  ·
                    rfl

theorem cell23_6492081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 1, 6].length) (baseStart_6492081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492081 prefixEnd_6492081 := by exact prefixLift 6492081
  have htrace : WordTrace (prefixWord ++ tailWord_6492081) baseStart_6492081 baseEnd_6492081 := by
    simpa [prefixWord, tailWord_6492081, baseEnd_6492081] using wordTrace_append hprefix tailTrace_6492081
  have hstable : (prefixWord ++ tailWord_6492081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492081).length < 2 ^ (prefixWord ++ tailWord_6492081).sum := by decide
  have hdescent : baseEnd_6492081 < baseStart_6492081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492111 : List Nat := [1, 1, 2, 1, 1, 5, 5, 1, 1, 5]
def baseStart_6492111 : Nat := 118140960795 + 6492111 * 2 ^ 59
def prefixEnd_6492111 : Nat := 4983230072969 + 3 ^ 40 * 6492111 * 2
def baseEnd_6492111 : Nat := 1111191135113784773185277

theorem tailTrace_6492111 : CollatzResearch.WordTrace tailWord_6492111 prefixEnd_6492111 1111191135113784773185277 := by
  unfold tailWord_6492111
  simp only [CollatzResearch.WordTrace]
  refine ⟨236786740983198086130676187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157857827322132057420450791 236786740983198086130676187)
  ·
    refine ⟨355180111474797129196014281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236786740983198086130676187 355180111474797129196014281)
    ·
      refine ⟨266385083606097846897010711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355180111474797129196014281 266385083606097846897010711)
      ·
        refine ⟨399577625409146770345516067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266385083606097846897010711 399577625409146770345516067)
        ·
          refine ⟨599366438113720155518274101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399577625409146770345516067 599366438113720155518274101)
          ·
            refine ⟨56190603573161264579838197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 599366438113720155518274101 56190603573161264579838197)
            ·
              refine ⟨5267869084983868554359831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56190603573161264579838197 5267869084983868554359831)
              ·
                refine ⟨7901803627475802831539747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5267869084983868554359831 7901803627475802831539747)
                ·
                  refine ⟨11852705441213704247309621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7901803627475802831539747 11852705441213704247309621)
                  ·
                    refine ⟨1111191135113784773185277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11852705441213704247309621 1111191135113784773185277)
                    ·
                      rfl

theorem cell23_6492111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 1, 5].length) (baseStart_6492111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492111 prefixEnd_6492111 := by exact prefixLift 6492111
  have htrace : WordTrace (prefixWord ++ tailWord_6492111) baseStart_6492111 baseEnd_6492111 := by
    simpa [prefixWord, tailWord_6492111, baseEnd_6492111] using wordTrace_append hprefix tailTrace_6492111
  have hstable : (prefixWord ++ tailWord_6492111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492111).length < 2 ^ (prefixWord ++ tailWord_6492111).sum := by decide
  have hdescent : baseEnd_6492111 < baseStart_6492111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492144 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 4]
def baseStart_6492144 : Nat := 118140960795 + 6492144 * 2 ^ 59
def prefixEnd_6492144 : Nat := 4983230072969 + 3 ^ 40 * 6492144 * 2
def baseEnd_6492144 : Nat := 3333590350202952690443179

theorem tailTrace_6492144 : CollatzResearch.WordTrace tailWord_6492144 prefixEnd_6492144 3333590350202952690443179 := by
  unfold tailWord_6492144
  simp only [CollatzResearch.WordTrace]
  refine ⟨118393972296039266383313743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157858629728052355177751657 118393972296039266383313743)
  ·
    refine ⟨177590958444058899574970615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118393972296039266383313743 177590958444058899574970615)
    ·
      refine ⟨266386437666088349362455923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177590958444058899574970615 266386437666088349362455923)
      ·
        refine ⟨399579656499132524043683885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266386437666088349362455923 399579656499132524043683885)
        ·
          refine ⟨149842371187174696516381457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399579656499132524043683885 149842371187174696516381457)
          ·
            refine ⟨112381778390381022387286093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149842371187174696516381457 112381778390381022387286093)
            ·
              refine ⟨42143166896392883395232285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112381778390381022387286093 42143166896392883395232285)
              ·
                refine ⟨15803687586147331273212107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42143166896392883395232285 15803687586147331273212107)
                ·
                  refine ⟨23705531379220996909818161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15803687586147331273212107 23705531379220996909818161)
                  ·
                    refine ⟨17779148534415747682363621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23705531379220996909818161 17779148534415747682363621)
                    ·
                      refine ⟨3333590350202952690443179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17779148534415747682363621 3333590350202952690443179)
                      ·
                        rfl

theorem cell23_6492144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 4].length) (baseStart_6492144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492144 prefixEnd_6492144 := by exact prefixLift 6492144
  have htrace : WordTrace (prefixWord ++ tailWord_6492144) baseStart_6492144 baseEnd_6492144 := by
    simpa [prefixWord, tailWord_6492144, baseEnd_6492144] using wordTrace_append hprefix tailTrace_6492144
  have hstable : (prefixWord ++ tailWord_6492144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492144).length < 2 ^ (prefixWord ++ tailWord_6492144).sum := by decide
  have hdescent : baseEnd_6492144 < baseStart_6492144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492147 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 7]
def baseStart_6492147 : Nat := 118140960795 + 6492147 * 2 ^ 59
def prefixEnd_6492147 : Nat := 4983230072969 + 3 ^ 40 * 6492147 * 2
def baseEnd_6492147 : Nat := 3333591890644916178705665

theorem tailTrace_6492147 : CollatzResearch.WordTrace tailWord_6492147 prefixEnd_6492147 3333591890644916178705665 := by
  unfold tailWord_6492147
  simp only [CollatzResearch.WordTrace]
  refine ⟨236788054011067664278986695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157858702674045109519324463 236788054011067664278986695)
  ·
    refine ⟨355182081016601496418480043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236788054011067664278986695 355182081016601496418480043)
    ·
      refine ⟨532773121524902244627720065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355182081016601496418480043 532773121524902244627720065)
      ·
        refine ⟨399579841143676683470790049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532773121524902244627720065 399579841143676683470790049)
        ·
          refine ⟨299684880857757512603092537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399579841143676683470790049 299684880857757512603092537)
          ·
            refine ⟨224763660643318134452319403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299684880857757512603092537 224763660643318134452319403)
            ·
              refine ⟨337145490964977201678479105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224763660643318134452319403 337145490964977201678479105)
              ·
                refine ⟨252859118223732901258859329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337145490964977201678479105 252859118223732901258859329)
                ·
                  refine ⟨189644338667799675944144497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252859118223732901258859329 189644338667799675944144497)
                  ·
                    refine ⟨142233254000849756958108373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 189644338667799675944144497 142233254000849756958108373)
                    ·
                      refine ⟨3333591890644916178705665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142233254000849756958108373 3333591890644916178705665)
                      ·
                        rfl

theorem cell23_6492147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_6492147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492147 prefixEnd_6492147 := by exact prefixLift 6492147
  have htrace : WordTrace (prefixWord ++ tailWord_6492147) baseStart_6492147 baseEnd_6492147 := by
    simpa [prefixWord, tailWord_6492147, baseEnd_6492147] using wordTrace_append hprefix tailTrace_6492147
  have hstable : (prefixWord ++ tailWord_6492147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492147).length < 2 ^ (prefixWord ++ tailWord_6492147).sum := by decide
  have hdescent : baseEnd_6492147 < baseStart_6492147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492165 : List Nat := [1, 3, 1, 1, 2, 4, 1, 5, 1, 2, 2]
def baseStart_6492165 : Nat := 118140960795 + 6492165 * 2 ^ 59
def prefixEnd_6492165 : Nat := 4983230072969 + 3 ^ 40 * 6492165 * 2
def baseEnd_6492165 : Nat := 3333601133296697108280583

theorem tailTrace_6492165 : CollatzResearch.WordTrace tailWord_6492165 prefixEnd_6492165 3333601133296697108280583 := by
  unfold tailWord_6492165
  simp only [CollatzResearch.WordTrace]
  refine ⟨236788710525002453353141949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157859140350001635568761299 236788710525002453353141949)
  ·
    refine ⟨88795766446875920007428231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236788710525002453353141949 88795766446875920007428231)
    ·
      refine ⟨133193649670313880011142347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88795766446875920007428231 133193649670313880011142347)
      ·
        refine ⟨199790474505470820016713521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133193649670313880011142347 199790474505470820016713521)
        ·
          refine ⟨149842855879103115012535141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199790474505470820016713521 149842855879103115012535141)
          ·
            refine ⟨28095535477331834064850339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149842855879103115012535141 28095535477331834064850339)
            ·
              refine ⟨42143303215997751097275509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28095535477331834064850339 42143303215997751097275509)
              ·
                refine ⟨3950934676499789165369579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42143303215997751097275509 3950934676499789165369579)
                ·
                  refine ⟨5926402014749683748054369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3950934676499789165369579 5926402014749683748054369)
                  ·
                    refine ⟨4444801511062262811040777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5926402014749683748054369 4444801511062262811040777)
                    ·
                      refine ⟨3333601133296697108280583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4444801511062262811040777 3333601133296697108280583)
                      ·
                        rfl

theorem cell23_6492165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 1, 2, 2].length) (baseStart_6492165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492165 prefixEnd_6492165 := by exact prefixLift 6492165
  have htrace : WordTrace (prefixWord ++ tailWord_6492165) baseStart_6492165 baseEnd_6492165 := by
    simpa [prefixWord, tailWord_6492165, baseEnd_6492165] using wordTrace_append hprefix tailTrace_6492165
  have hstable : (prefixWord ++ tailWord_6492165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492165).length < 2 ^ (prefixWord ++ tailWord_6492165).sum := by decide
  have hdescent : baseEnd_6492165 < baseStart_6492165 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492208 : List Nat := [2, 1, 1, 1, 2, 5, 1, 4, 1, 3, 2]
def baseStart_6492208 : Nat := 118140960795 + 6492208 * 2 ^ 59
def prefixEnd_6492208 : Nat := 4983230072969 + 3 ^ 40 * 6492208 * 2
def baseEnd_6492208 : Nat := 3333623212964840440042885

theorem tailTrace_6492208 : CollatzResearch.WordTrace tailWord_6492208 prefixEnd_6492208 3333623212964840440042885 := by
  unfold tailWord_6492208
  simp only [CollatzResearch.WordTrace]
  refine ⟨118395139431923335848478639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157860185909231114464638185 118395139431923335848478639)
  ·
    refine ⟨177592709147885003772717959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118395139431923335848478639 177592709147885003772717959)
    ·
      refine ⟨266389063721827505659076939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177592709147885003772717959 266389063721827505659076939)
      ·
        refine ⟨399583595582741258488615409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266389063721827505659076939 399583595582741258488615409)
        ·
          refine ⟨299687696687055943866461557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399583595582741258488615409 299687696687055943866461557)
          ·
            refine ⟨28095721564411494737480771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 299687696687055943866461557 28095721564411494737480771)
            ·
              refine ⟨42143582346617242106221157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28095721564411494737480771 42143582346617242106221157)
              ·
                refine ⟨7901921689990732894916467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42143582346617242106221157 7901921689990732894916467)
                ·
                  refine ⟨11852882534986099342374701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7901921689990732894916467 11852882534986099342374701)
                  ·
                    refine ⟨4444830950619787253390513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11852882534986099342374701 4444830950619787253390513)
                    ·
                      refine ⟨3333623212964840440042885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4444830950619787253390513 3333623212964840440042885)
                      ·
                        rfl

theorem cell23_6492208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 1, 3, 2].length) (baseStart_6492208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492208 prefixEnd_6492208 := by exact prefixLift 6492208
  have htrace : WordTrace (prefixWord ++ tailWord_6492208) baseStart_6492208 baseEnd_6492208 := by
    simpa [prefixWord, tailWord_6492208, baseEnd_6492208] using wordTrace_append hprefix tailTrace_6492208
  have hstable : (prefixWord ++ tailWord_6492208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492208).length < 2 ^ (prefixWord ++ tailWord_6492208).sum := by decide
  have hdescent : baseEnd_6492208 < baseStart_6492208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492224 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 5]
def baseStart_6492224 : Nat := 118140960795 + 6492224 * 2 ^ 59
def prefixEnd_6492224 : Nat := 4983230072969 + 3 ^ 40 * 6492224 * 2
def baseEnd_6492224 : Nat := 3333631428655312377442811

theorem tailTrace_6492224 : CollatzResearch.WordTrace tailWord_6492224 prefixEnd_6492224 3333631428655312377442811 := by
  unfold tailWord_6492224
  simp only [CollatzResearch.WordTrace]
  refine ⟨118395431215894353214769863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157860574954525804286359817 118395431215894353214769863)
  ·
    refine ⟨177593146823841529822154795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118395431215894353214769863 177593146823841529822154795)
    ·
      refine ⟨266389720235762294733232193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177593146823841529822154795 266389720235762294733232193)
      ·
        refine ⟨199792290176821721049924145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266389720235762294733232193 199792290176821721049924145)
        ·
          refine ⟨149844217632616290787443109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199792290176821721049924145 149844217632616290787443109)
          ·
            refine ⟨28095790806115554522645583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149844217632616290787443109 28095790806115554522645583)
            ·
              refine ⟨42143686209173331783968375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28095790806115554522645583 42143686209173331783968375)
              ·
                refine ⟨63215529313759997675952563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42143686209173331783968375 63215529313759997675952563)
                ·
                  refine ⟨94823293970639996513928845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63215529313759997675952563 94823293970639996513928845)
                  ·
                    refine ⟨35558735238989998692723317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94823293970639996513928845 35558735238989998692723317)
                    ·
                      refine ⟨3333631428655312377442811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35558735238989998692723317 3333631428655312377442811)
                      ·
                        rfl

theorem cell23_6492224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_6492224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492224 prefixEnd_6492224 := by exact prefixLift 6492224
  have htrace : WordTrace (prefixWord ++ tailWord_6492224) baseStart_6492224 baseEnd_6492224 := by
    simpa [prefixWord, tailWord_6492224, baseEnd_6492224] using wordTrace_append hprefix tailTrace_6492224
  have hstable : (prefixWord ++ tailWord_6492224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492224).length < 2 ^ (prefixWord ++ tailWord_6492224).sum := by decide
  have hdescent : baseEnd_6492224 < baseStart_6492224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492225 : List Nat := [1, 2, 5, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_6492225 : Nat := 118140960795 + 6492225 * 2 ^ 59
def prefixEnd_6492225 : Nat := 4983230072969 + 3 ^ 40 * 6492225 * 2
def baseEnd_6492225 : Nat := 3333631942135966873530307

theorem tailTrace_6492225 : CollatzResearch.WordTrace tailWord_6492225 prefixEnd_6492225 3333631942135966873530307 := by
  unfold tailWord_6492225
  simp only [CollatzResearch.WordTrace]
  refine ⟨236790898904785083600326129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157860599269856722400217419 236790898904785083600326129)
  ·
    refine ⟨177593174178588812700244597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236790898904785083600326129 177593174178588812700244597)
    ·
      refine ⟨16649360079242701190647931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 177593174178588812700244597 16649360079242701190647931)
      ·
        refine ⟨24974040118864051785971897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16649360079242701190647931 24974040118864051785971897)
        ·
          refine ⟨18730530089148038839478923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24974040118864051785971897 18730530089148038839478923)
          ·
            refine ⟨28095795133722058259218385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18730530089148038839478923 28095795133722058259218385)
            ·
              refine ⟨21071846350291543694413789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28095795133722058259218385 21071846350291543694413789)
              ·
                refine ⟨7901942381359328885405171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21071846350291543694413789 7901942381359328885405171)
                ·
                  refine ⟨11852913572038993328107757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7901942381359328885405171 11852913572038993328107757)
                  ·
                    refine ⟨4444842589514622498040409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11852913572038993328107757 4444842589514622498040409)
                    ·
                      refine ⟨3333631942135966873530307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4444842589514622498040409 3333631942135966873530307)
                      ·
                        rfl

theorem cell23_6492225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_6492225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492225 prefixEnd_6492225 := by exact prefixLift 6492225
  have htrace : WordTrace (prefixWord ++ tailWord_6492225) baseStart_6492225 baseEnd_6492225 := by
    simpa [prefixWord, tailWord_6492225, baseEnd_6492225] using wordTrace_append hprefix tailTrace_6492225
  have hstable : (prefixWord ++ tailWord_6492225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492225).length < 2 ^ (prefixWord ++ tailWord_6492225).sum := by decide
  have hdescent : baseEnd_6492225 < baseStart_6492225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492291 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 2, 5]
def baseStart_6492291 : Nat := 118140960795 + 6492291 * 2 ^ 59
def prefixEnd_6492291 : Nat := 4983230072969 + 3 ^ 40 * 6492291 * 2
def baseEnd_6492291 : Nat := 1111221943953054538435001

theorem tailTrace_6492291 : CollatzResearch.WordTrace tailWord_6492291 prefixEnd_6492291 1111221943953054538435001 := by
  unfold tailWord_6492291
  simp only [CollatzResearch.WordTrace]
  refine ⟨236793306122545976872228727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157862204081697317914819151 236793306122545976872228727)
  ·
    refine ⟨355189959183818965308343091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236793306122545976872228727 355189959183818965308343091)
    ·
      refine ⟨532784938775728447962514637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355189959183818965308343091 532784938775728447962514637)
      ·
        refine ⟨199794352040898167985942989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 532784938775728447962514637 199794352040898167985942989)
        ·
          refine ⟨74922882015336812994728621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199794352040898167985942989 74922882015336812994728621)
          ·
            refine ⟨28096080755751304873023233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74922882015336812994728621 28096080755751304873023233)
            ·
              refine ⟨21072060566813478654767425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28096080755751304873023233 21072060566813478654767425)
              ·
                refine ⟨15804045425110108991075569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21072060566813478654767425 15804045425110108991075569)
                ·
                  refine ⟨11853034068832581743306677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15804045425110108991075569 11853034068832581743306677)
                  ·
                    refine ⟨1111221943953054538435001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11853034068832581743306677 1111221943953054538435001)
                    ·
                      rfl

theorem cell23_6492291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 5].length) (baseStart_6492291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492291 prefixEnd_6492291 := by exact prefixLift 6492291
  have htrace : WordTrace (prefixWord ++ tailWord_6492291) baseStart_6492291 baseEnd_6492291 := by
    simpa [prefixWord, tailWord_6492291, baseEnd_6492291] using wordTrace_append hprefix tailTrace_6492291
  have hstable : (prefixWord ++ tailWord_6492291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492291).length < 2 ^ (prefixWord ++ tailWord_6492291).sum := by decide
  have hdescent : baseEnd_6492291 < baseStart_6492291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492298 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 2, 5, 2]
def baseStart_6492298 : Nat := 118140960795 + 6492298 * 2 ^ 59
def prefixEnd_6492298 : Nat := 4983230072969 + 3 ^ 40 * 6492298 * 2
def baseEnd_6492298 : Nat := 3333669426223745087917471

theorem tailTrace_6492298 : CollatzResearch.WordTrace tailWord_6492298 prefixEnd_6492298 3333669426223745087917471 := by
  unfold tailWord_6492298
  simp only [CollatzResearch.WordTrace]
  refine ⟨59198390358380154266933387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157862374289013744711822365 59198390358380154266933387)
  ·
    refine ⟨88797585537570231400400081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59198390358380154266933387 88797585537570231400400081)
    ·
      refine ⟨66598189153177673550300061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88797585537570231400400081 66598189153177673550300061)
      ·
        refine ⟨24974320932441627581362523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66598189153177673550300061 24974320932441627581362523)
        ·
          refine ⟨37461481398662441372043785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24974320932441627581362523 37461481398662441372043785)
          ·
            refine ⟨28096111048996831029032839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37461481398662441372043785 28096111048996831029032839)
            ·
              refine ⟨42144166573495246543549259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28096111048996831029032839 42144166573495246543549259)
              ·
                refine ⟨63216249860242869815323889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42144166573495246543549259 63216249860242869815323889)
                ·
                  refine ⟨47412187395182152361492917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63216249860242869815323889 47412187395182152361492917)
                  ·
                    refine ⟨4444892568298326783889961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47412187395182152361492917 4444892568298326783889961)
                    ·
                      refine ⟨3333669426223745087917471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4444892568298326783889961 3333669426223745087917471)
                      ·
                        rfl

theorem cell23_6492298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_6492298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492298 prefixEnd_6492298 := by exact prefixLift 6492298
  have htrace : WordTrace (prefixWord ++ tailWord_6492298) baseStart_6492298 baseEnd_6492298 := by
    simpa [prefixWord, tailWord_6492298, baseEnd_6492298] using wordTrace_append hprefix tailTrace_6492298
  have hstable : (prefixWord ++ tailWord_6492298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492298).length < 2 ^ (prefixWord ++ tailWord_6492298).sum := by decide
  have hdescent : baseEnd_6492298 < baseStart_6492298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492340 : List Nat := [2, 5, 3, 1, 2, 1, 1, 2, 2, 2, 2]
def baseStart_6492340 : Nat := 118140960795 + 6492340 * 2 ^ 59
def prefixEnd_6492340 : Nat := 4983230072969 + 3 ^ 40 * 6492340 * 2
def baseEnd_6492340 : Nat := 3333690992411233923592279

theorem tailTrace_6492340 : CollatzResearch.WordTrace tailWord_6492340 prefixEnd_6492340 3333690992411233923592279 := by
  unfold tailWord_6492340
  simp only [CollatzResearch.WordTrace]
  refine ⟨118397546649684229120381237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157863395532912305493841649 118397546649684229120381237)
  ·
    refine ⟨11099769998407896480035741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118397546649684229120381237 11099769998407896480035741)
    ·
      refine ⟨4162413749402961180013403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11099769998407896480035741 4162413749402961180013403)
      ·
        refine ⟨6243620624104441770020105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4162413749402961180013403 6243620624104441770020105)
        ·
          refine ⟨4682715468078331327515079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6243620624104441770020105 4682715468078331327515079)
          ·
            refine ⟨7024073202117496991272619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4682715468078331327515079 7024073202117496991272619)
            ·
              refine ⟨10536109803176245486908929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7024073202117496991272619 10536109803176245486908929)
              ·
                refine ⟨7902082352382184115181697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10536109803176245486908929 7902082352382184115181697)
                ·
                  refine ⟨5926561764286638086386273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7902082352382184115181697 5926561764286638086386273)
                  ·
                    refine ⟨4444921323214978564789705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5926561764286638086386273 4444921323214978564789705)
                    ·
                      refine ⟨3333690992411233923592279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4444921323214978564789705 3333690992411233923592279)
                      ·
                        rfl

theorem cell23_6492340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_6492340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492340 prefixEnd_6492340 := by exact prefixLift 6492340
  have htrace : WordTrace (prefixWord ++ tailWord_6492340) baseStart_6492340 baseEnd_6492340 := by
    simpa [prefixWord, tailWord_6492340, baseEnd_6492340] using wordTrace_append hprefix tailTrace_6492340
  have hstable : (prefixWord ++ tailWord_6492340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492340).length < 2 ^ (prefixWord ++ tailWord_6492340).sum := by decide
  have hdescent : baseEnd_6492340 < baseStart_6492340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492412 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 3, 1, 3]
def baseStart_6492412 : Nat := 118140960795 + 6492412 * 2 ^ 59
def prefixEnd_6492412 : Nat := 4983230072969 + 3 ^ 40 * 6492412 * 2
def baseEnd_6492412 : Nat := 3333727963018357641891947

theorem tailTrace_6492412 : CollatzResearch.WordTrace tailWord_6492412 prefixEnd_6492412 3333727963018357641891947 := by
  unfold tailWord_6492412
  simp only [CollatzResearch.WordTrace]
  refine ⟨118398859677553807268691745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157865146236738409691588993 118398859677553807268691745)
  ·
    refine ⟨88799144758165355451518809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118398859677553807268691745 88799144758165355451518809)
    ·
      refine ⟨66599358568624016588639107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88799144758165355451518809 66599358568624016588639107)
      ·
        refine ⟨99899037852936024882958661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66599358568624016588639107 99899037852936024882958661)
        ·
          refine ⟨18731069597425504665554749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99899037852936024882958661 18731069597425504665554749)
          ·
            refine ⟨7024151099034564249583031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18731069597425504665554749 7024151099034564249583031)
            ·
              refine ⟨10536226648551846374374547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7024151099034564249583031 10536226648551846374374547)
              ·
                refine ⟨15804339972827769561561821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10536226648551846374374547 15804339972827769561561821)
                ·
                  refine ⟨5926627489810413585585683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15804339972827769561561821 5926627489810413585585683)
                  ·
                    refine ⟨8889941234715620378378525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5926627489810413585585683 8889941234715620378378525)
                    ·
                      refine ⟨3333727963018357641891947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8889941234715620378378525 3333727963018357641891947)
                      ·
                        rfl

theorem cell23_6492412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_6492412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492412 prefixEnd_6492412 := by exact prefixLift 6492412
  have htrace : WordTrace (prefixWord ++ tailWord_6492412) baseStart_6492412 baseEnd_6492412 := by
    simpa [prefixWord, tailWord_6492412, baseEnd_6492412] using wordTrace_append hprefix tailTrace_6492412
  have hstable : (prefixWord ++ tailWord_6492412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492412).length < 2 ^ (prefixWord ++ tailWord_6492412).sum := by decide
  have hdescent : baseEnd_6492412 < baseStart_6492412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492421 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 3, 1, 5]
def baseStart_6492421 : Nat := 118140960795 + 6492421 * 2 ^ 59
def prefixEnd_6492421 : Nat := 4983230072969 + 3 ^ 40 * 6492421 * 2
def baseEnd_6492421 : Nat := 3333732584344248106679405

theorem tailTrace_6492421 : CollatzResearch.WordTrace tailWord_6492421 prefixEnd_6492421 3333732584344248106679405 := by
  unfold tailWord_6492421
  simp only [CollatzResearch.WordTrace]
  refine ⟨236798047612075009074461117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157865365074716672716307411 236798047612075009074461117)
  ·
    refine ⟨88799267854528128402922919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236798047612075009074461117 88799267854528128402922919)
    ·
      refine ⟨133198901781792192604384379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88799267854528128402922919 133198901781792192604384379)
      ·
        refine ⟨199798352672688288906576569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133198901781792192604384379 199798352672688288906576569)
        ·
          refine ⟨149848764504516216679932427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199798352672688288906576569 149848764504516216679932427)
          ·
            refine ⟨224773146756774325019898641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149848764504516216679932427 224773146756774325019898641)
            ·
              refine ⟨168579860067580743764923981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224773146756774325019898641 168579860067580743764923981)
              ·
                refine ⟨63217447525342778911846493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168579860067580743764923981 63217447525342778911846493)
                ·
                  refine ⟨23706542822003542091942435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63217447525342778911846493 23706542822003542091942435)
                  ·
                    refine ⟨35559814233005313137913653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23706542822003542091942435 35559814233005313137913653)
                    ·
                      refine ⟨3333732584344248106679405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35559814233005313137913653 3333732584344248106679405)
                      ·
                        rfl

theorem cell23_6492421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_6492421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492421 prefixEnd_6492421 := by exact prefixLift 6492421
  have htrace : WordTrace (prefixWord ++ tailWord_6492421) baseStart_6492421 baseEnd_6492421 := by
    simpa [prefixWord, tailWord_6492421, baseEnd_6492421] using wordTrace_append hprefix tailTrace_6492421
  have hstable : (prefixWord ++ tailWord_6492421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492421).length < 2 ^ (prefixWord ++ tailWord_6492421).sum := by decide
  have hdescent : baseEnd_6492421 < baseStart_6492421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492431 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 4]
def baseStart_6492431 : Nat := 118140960795 + 6492431 * 2 ^ 59
def prefixEnd_6492431 : Nat := 4983230072969 + 3 ^ 40 * 6492431 * 2
def baseEnd_6492431 : Nat := 3333737719150793067554359

theorem tailTrace_6492431 : CollatzResearch.WordTrace tailWord_6492431 prefixEnd_6492431 3333737719150793067554359 := by
  unfold tailWord_6492431
  simp only [CollatzResearch.WordTrace]
  refine ⟨236798412342038780782325147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157865608228025853854883431 236798412342038780782325147)
  ·
    refine ⟨355197618513058171173487721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236798412342038780782325147 355197618513058171173487721)
    ·
      refine ⟨266398213884793628380115791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355197618513058171173487721 266398213884793628380115791)
      ·
        refine ⟨399597320827190442570173687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266398213884793628380115791 399597320827190442570173687)
        ·
          refine ⟨599395981240785663855260531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399597320827190442570173687 599395981240785663855260531)
          ·
            refine ⟨899093971861178495782890797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599395981240785663855260531 899093971861178495782890797)
            ·
              refine ⟨337160239447941935918584049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 899093971861178495782890797 337160239447941935918584049)
              ·
                refine ⟨252870179585956451938938037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337160239447941935918584049 252870179585956451938938037)
                ·
                  refine ⟨23706579336183417369275441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 252870179585956451938938037 23706579336183417369275441)
                  ·
                    refine ⟨17779934502137563026956581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23706579336183417369275441 17779934502137563026956581)
                    ·
                      refine ⟨3333737719150793067554359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17779934502137563026956581 3333737719150793067554359)
                      ·
                        rfl

theorem cell23_6492431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_6492431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492431 prefixEnd_6492431 := by exact prefixLift 6492431
  have htrace : WordTrace (prefixWord ++ tailWord_6492431) baseStart_6492431 baseEnd_6492431 := by
    simpa [prefixWord, tailWord_6492431, baseEnd_6492431] using wordTrace_append hprefix tailTrace_6492431
  have hstable : (prefixWord ++ tailWord_6492431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492431).length < 2 ^ (prefixWord ++ tailWord_6492431).sum := by decide
  have hdescent : baseEnd_6492431 < baseStart_6492431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492435 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 3, 2, 2]
def baseStart_6492435 : Nat := 118140960795 + 6492435 * 2 ^ 59
def prefixEnd_6492435 : Nat := 4983230072969 + 3 ^ 40 * 6492435 * 2
def baseEnd_6492435 : Nat := 3333739773073411051904341

theorem tailTrace_6492435 : CollatzResearch.WordTrace tailWord_6492435 prefixEnd_6492435 3333739773073411051904341 := by
  unfold tailWord_6492435
  simp only [CollatzResearch.WordTrace]
  refine ⟨236798558234024289465470759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157865705489349526310313839 236798558234024289465470759)
  ·
    refine ⟨355197837351036434198206139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236798558234024289465470759 355197837351036434198206139)
    ·
      refine ⟨532796756026554651297309209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355197837351036434198206139 532796756026554651297309209)
      ·
        refine ⟨399597567019915988472981907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532796756026554651297309209 399597567019915988472981907)
        ·
          refine ⟨599396350529873982709472861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399597567019915988472981907 599396350529873982709472861)
          ·
            refine ⟨224773631448702743516052323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 599396350529873982709472861 224773631448702743516052323)
            ·
              refine ⟨337160447173054115274078485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224773631448702743516052323 337160447173054115274078485)
              ·
                refine ⟨15804395961236911653472429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 337160447173054115274078485 15804395961236911653472429)
                ·
                  refine ⟨5926648485463841870052161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15804395961236911653472429 5926648485463841870052161)
                  ·
                    refine ⟨4444986364097881402539121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5926648485463841870052161 4444986364097881402539121)
                    ·
                      refine ⟨3333739773073411051904341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4444986364097881402539121 3333739773073411051904341)
                      ·
                        rfl

theorem cell23_6492435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 2, 2].length) (baseStart_6492435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492435 prefixEnd_6492435 := by exact prefixLift 6492435
  have htrace : WordTrace (prefixWord ++ tailWord_6492435) baseStart_6492435 baseEnd_6492435 := by
    simpa [prefixWord, tailWord_6492435, baseEnd_6492435] using wordTrace_append hprefix tailTrace_6492435
  have hstable : (prefixWord ++ tailWord_6492435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492435).length < 2 ^ (prefixWord ++ tailWord_6492435).sum := by decide
  have hdescent : baseEnd_6492435 < baseStart_6492435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492445 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 1, 6]
def baseStart_6492445 : Nat := 118140960795 + 6492445 * 2 ^ 59
def prefixEnd_6492445 : Nat := 4983230072969 + 3 ^ 40 * 6492445 * 2
def baseEnd_6492445 : Nat := 1111248302626652004259765

theorem tailTrace_6492445 : CollatzResearch.WordTrace tailWord_6492445 prefixEnd_6492445 1111248302626652004259765 := by
  unfold tailWord_6492445
  simp only [CollatzResearch.WordTrace]
  refine ⟨236798922963988061173334789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157865948642658707448889859 236798922963988061173334789)
  ·
    refine ⟨44399798055747761470000273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236798922963988061173334789 44399798055747761470000273)
    ·
      refine ⟨33299848541810821102500205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44399798055747761470000273 33299848541810821102500205)
      ·
        refine ⟨12487443203179057913437577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33299848541810821102500205 12487443203179057913437577)
        ·
          refine ⟨9365582402384293435078183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12487443203179057913437577 9365582402384293435078183)
          ·
            refine ⟨14048373603576440152617275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9365582402384293435078183 14048373603576440152617275)
            ·
              refine ⟨21072560405364660228925913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14048373603576440152617275 21072560405364660228925913)
              ·
                refine ⟨15804420304023495171694435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21072560405364660228925913 15804420304023495171694435)
                ·
                  refine ⟨23706630456035242757541653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15804420304023495171694435 23706630456035242757541653)
                  ·
                    refine ⟨1111248302626652004259765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23706630456035242757541653 1111248302626652004259765)
                    ·
                      rfl

theorem cell23_6492445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_6492445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492445 prefixEnd_6492445 := by exact prefixLift 6492445
  have htrace : WordTrace (prefixWord ++ tailWord_6492445) baseStart_6492445 baseEnd_6492445 := by
    simpa [prefixWord, tailWord_6492445, baseEnd_6492445] using wordTrace_append hprefix tailTrace_6492445
  have hstable : (prefixWord ++ tailWord_6492445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492445).length < 2 ^ (prefixWord ++ tailWord_6492445).sum := by decide
  have hdescent : baseEnd_6492445 < baseStart_6492445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492448 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 4]
def baseStart_6492448 : Nat := 118140960795 + 6492448 * 2 ^ 59
def prefixEnd_6492448 : Nat := 4983230072969 + 3 ^ 40 * 6492448 * 2
def baseEnd_6492448 : Nat := 3333746448321919501041781

theorem tailTrace_6492448 : CollatzResearch.WordTrace tailWord_6492448 prefixEnd_6492448 3333746448321919501041781 := by
  unfold tailWord_6492448
  simp only [CollatzResearch.WordTrace]
  refine ⟨118399516191488596342846999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157866021588651461790462665 118399516191488596342846999)
  ·
    refine ⟨177599274287232894514270499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118399516191488596342846999 177599274287232894514270499)
    ·
      refine ⟨266398911430849341771405749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177599274287232894514270499 266398911430849341771405749)
      ·
        refine ⟨24974897946642125791069289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 266398911430849341771405749 24974897946642125791069289)
        ·
          refine ⟨18731173459981594343301967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24974897946642125791069289 18731173459981594343301967)
          ·
            refine ⟨28096760189972391514952951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18731173459981594343301967 28096760189972391514952951)
            ·
              refine ⟨42145140284958587272429427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28096760189972391514952951 42145140284958587272429427)
              ·
                refine ⟨63217710427437880908644141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42145140284958587272429427 63217710427437880908644141)
                ·
                  refine ⟨23706641410289205340741553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63217710427437880908644141 23706641410289205340741553)
                  ·
                    refine ⟨17779981057716904005556165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23706641410289205340741553 17779981057716904005556165)
                    ·
                      refine ⟨3333746448321919501041781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17779981057716904005556165 3333746448321919501041781)
                      ·
                        rfl

theorem cell23_6492448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_6492448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492448 prefixEnd_6492448 := by exact prefixLift 6492448
  have htrace : WordTrace (prefixWord ++ tailWord_6492448) baseStart_6492448 baseEnd_6492448 := by
    simpa [prefixWord, tailWord_6492448, baseEnd_6492448] using wordTrace_append hprefix tailTrace_6492448
  have hstable : (prefixWord ++ tailWord_6492448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492448).length < 2 ^ (prefixWord ++ tailWord_6492448).sum := by decide
  have hdescent : baseEnd_6492448 < baseStart_6492448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492452 : List Nat := [2, 3, 1, 3, 1, 3, 3, 1, 1, 1, 4]
def baseStart_6492452 : Nat := 118140960795 + 6492452 * 2 ^ 59
def prefixEnd_6492452 : Nat := 4983230072969 + 3 ^ 40 * 6492452 * 2
def baseEnd_6492452 : Nat := 3333748502244537485391763

theorem tailTrace_6492452 : CollatzResearch.WordTrace tailWord_6492452 prefixEnd_6492452 3333748502244537485391763 := by
  unfold tailWord_6492452
  simp only [CollatzResearch.WordTrace]
  refine ⟨118399589137481350684419805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157866118849975134245893073 118399589137481350684419805)
  ·
    refine ⟨44399845926555506506657427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118399589137481350684419805 44399845926555506506657427)
    ·
      refine ⟨66599768889833259759986141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44399845926555506506657427 66599768889833259759986141)
      ·
        refine ⟨24974913333687472409994803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66599768889833259759986141 24974913333687472409994803)
        ·
          refine ⟨37462370000531208614992205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24974913333687472409994803 37462370000531208614992205)
          ·
            refine ⟨14048388750199203230622077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37462370000531208614992205 14048388750199203230622077)
            ·
              refine ⟨5268145781324701211483279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14048388750199203230622077 5268145781324701211483279)
              ·
                refine ⟨7902218671987051817224919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5268145781324701211483279 7902218671987051817224919)
                ·
                  refine ⟨11853328007980577725837379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7902218671987051817224919 11853328007980577725837379)
                  ·
                    refine ⟨17779992011970866588756069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11853328007980577725837379 17779992011970866588756069)
                    ·
                      refine ⟨3333748502244537485391763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17779992011970866588756069 3333748502244537485391763)
                      ·
                        rfl

theorem cell23_6492452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_6492452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492452 prefixEnd_6492452 := by exact prefixLift 6492452
  have htrace : WordTrace (prefixWord ++ tailWord_6492452) baseStart_6492452 baseEnd_6492452 := by
    simpa [prefixWord, tailWord_6492452, baseEnd_6492452] using wordTrace_append hprefix tailTrace_6492452
  have hstable : (prefixWord ++ tailWord_6492452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492452).length < 2 ^ (prefixWord ++ tailWord_6492452).sum := by decide
  have hdescent : baseEnd_6492452 < baseStart_6492452 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492458 : List Nat := [3, 1, 4, 2, 2, 11]
def baseStart_6492458 : Nat := 118140960795 + 6492458 * 2 ^ 59
def prefixEnd_6492458 : Nat := 4983230072969 + 3 ^ 40 * 6492458 * 2
def baseEnd_6492458 : Nat := 13719142317401088320645

theorem tailTrace_6492458 : CollatzResearch.WordTrace tailWord_6492458 prefixEnd_6492458 13719142317401088320645 := by
  unfold tailWord_6492458
  simp only [CollatzResearch.WordTrace]
  refine ⟨59199849278235241098389507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157866264741960642929038685 59199849278235241098389507)
  ·
    refine ⟨88799773917352861647584261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59199849278235241098389507 88799773917352861647584261)
    ·
      refine ⟨16649957609503661558922049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88799773917352861647584261 16649957609503661558922049)
      ·
        refine ⟨12487468207127746169191537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16649957609503661558922049 12487468207127746169191537)
        ·
          refine ⟨9365601155345809626893653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12487468207127746169191537 9365601155345809626893653)
          ·
            refine ⟨13719142317401088320645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9365601155345809626893653 13719142317401088320645)
            ·
              rfl

theorem cell23_6492458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 11].length) (baseStart_6492458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492458 prefixEnd_6492458 := by exact prefixLift 6492458
  have htrace : WordTrace (prefixWord ++ tailWord_6492458) baseStart_6492458 baseEnd_6492458 := by
    simpa [prefixWord, tailWord_6492458, baseEnd_6492458] using wordTrace_append hprefix tailTrace_6492458
  have hstable : (prefixWord ++ tailWord_6492458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492458).length < 2 ^ (prefixWord ++ tailWord_6492458).sum := by decide
  have hdescent : baseEnd_6492458 < baseStart_6492458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492469 : List Nat := [1, 3, 3, 1, 2, 1, 3, 4, 1, 2, 2]
def baseStart_6492469 : Nat := 118140960795 + 6492469 * 2 ^ 59
def prefixEnd_6492469 : Nat := 4983230072969 + 3 ^ 40 * 6492469 * 2
def baseEnd_6492469 : Nat := 3333757231415663918879185

theorem tailTrace_6492469 : CollatzResearch.WordTrace tailWord_6492469 prefixEnd_6492469 3333757231415663918879185 := by
  unfold tailWord_6492469
  simp only [CollatzResearch.WordTrace]
  refine ⟨236799798315901113272208461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157866532210600742181472307 236799798315901113272208461)
  ·
    refine ⟨88799924368462917477078173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236799798315901113272208461 88799924368462917477078173)
    ·
      refine ⟨33299971638173594053904315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88799924368462917477078173 33299971638173594053904315)
      ·
        refine ⟨49949957457260391080856473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33299971638173594053904315 49949957457260391080856473)
        ·
          refine ⟨37462468092945293310642355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49949957457260391080856473 37462468092945293310642355)
          ·
            refine ⟨56193702139417939965963533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37462468092945293310642355 56193702139417939965963533)
            ·
              refine ⟨21072638302281727487236325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56193702139417939965963533 21072638302281727487236325)
              ·
                refine ⟨3951119681677823903856811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21072638302281727487236325 3951119681677823903856811)
                ·
                  refine ⟨5926679522516735855785217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3951119681677823903856811 5926679522516735855785217)
                  ·
                    refine ⟨4445009641887551891838913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5926679522516735855785217 4445009641887551891838913)
                    ·
                      refine ⟨3333757231415663918879185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4445009641887551891838913 3333757231415663918879185)
                      ·
                        rfl

theorem cell23_6492469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_6492469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492469 prefixEnd_6492469 := by exact prefixLift 6492469
  have htrace : WordTrace (prefixWord ++ tailWord_6492469) baseStart_6492469 baseEnd_6492469 := by
    simpa [prefixWord, tailWord_6492469, baseEnd_6492469] using wordTrace_append hprefix tailTrace_6492469
  have hstable : (prefixWord ++ tailWord_6492469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492469).length < 2 ^ (prefixWord ++ tailWord_6492469).sum := by decide
  have hdescent : baseEnd_6492469 < baseStart_6492469 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492519 : List Nat := [1, 1, 5, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_6492519 : Nat := 118140960795 + 6492519 * 2 ^ 59
def prefixEnd_6492519 : Nat := 4983230072969 + 3 ^ 40 * 6492519 * 2
def baseEnd_6492519 : Nat := 3333782905448388723253955

theorem tailTrace_6492519 : CollatzResearch.WordTrace tailWord_6492519 prefixEnd_6492519 3333782905448388723253955 := by
  unfold tailWord_6492519
  simp only [CollatzResearch.WordTrace]
  refine ⟨236801621965719971811528611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157867747977146647874352407 236801621965719971811528611)
  ·
    refine ⟨355202432948579957717292917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236801621965719971811528611 355202432948579957717292917)
    ·
      refine ⟨33300228088929371035996211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 355202432948579957717292917 33300228088929371035996211)
      ·
        refine ⟨49950342133394056553994317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33300228088929371035996211 49950342133394056553994317)
        ·
          refine ⟨18731378300022771207747869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49950342133394056553994317 18731378300022771207747869)
          ·
            refine ⟨7024266862508539202905451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18731378300022771207747869 7024266862508539202905451)
            ·
              refine ⟨10536400293762808804358177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7024266862508539202905451 10536400293762808804358177)
              ·
                refine ⟨7902300220322106603268633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10536400293762808804358177 7902300220322106603268633)
                ·
                  refine ⟨5926725165241579952451475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7902300220322106603268633 5926725165241579952451475)
                  ·
                    refine ⟨8890087747862369928677213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5926725165241579952451475 8890087747862369928677213)
                    ·
                      refine ⟨3333782905448388723253955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8890087747862369928677213 3333782905448388723253955)
                      ·
                        rfl

theorem cell23_6492519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_6492519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492519 prefixEnd_6492519 := by exact prefixLift 6492519
  have htrace : WordTrace (prefixWord ++ tailWord_6492519) baseStart_6492519 baseEnd_6492519 := by
    simpa [prefixWord, tailWord_6492519, baseEnd_6492519] using wordTrace_append hprefix tailTrace_6492519
  have hstable : (prefixWord ++ tailWord_6492519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492519).length < 2 ^ (prefixWord ++ tailWord_6492519).sum := by decide
  have hdescent : baseEnd_6492519 < baseStart_6492519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492531 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 11]
def baseStart_6492531 : Nat := 118140960795 + 6492531 * 2 ^ 59
def prefixEnd_6492531 : Nat := 4983230072969 + 3 ^ 40 * 6492531 * 2
def baseEnd_6492531 : Nat := 370421007468471408478211

theorem tailTrace_6492531 : CollatzResearch.WordTrace tailWord_6492531 prefixEnd_6492531 370421007468471408478211 := by
  unfold tailWord_6492531
  simp only [CollatzResearch.WordTrace]
  refine ⟨236802059641676497860965447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157868039761117665240643631 236802059641676497860965447)
  ·
    refine ⟨355203089462514746791448171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236802059641676497860965447 355203089462514746791448171)
    ·
      refine ⟨532804634193772120187172257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355203089462514746791448171 532804634193772120187172257)
      ·
        refine ⟨399603475645329090140379193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532804634193772120187172257 399603475645329090140379193)
        ·
          refine ⟨299702606733996817605284395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399603475645329090140379193 299702606733996817605284395)
          ·
            refine ⟨449553910100995226407926593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299702606733996817605284395 449553910100995226407926593)
            ·
              refine ⟨337165432575746419805944945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449553910100995226407926593 337165432575746419805944945)
              ·
                refine ⟨252874074431809814854458709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337165432575746419805944945 252874074431809814854458709)
                ·
                  refine ⟨370421007468471408478211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 252874074431809814854458709 370421007468471408478211)
                  ·
                    rfl

theorem cell23_6492531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 11].length) (baseStart_6492531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492531 prefixEnd_6492531 := by exact prefixLift 6492531
  have htrace : WordTrace (prefixWord ++ tailWord_6492531) baseStart_6492531 baseEnd_6492531 := by
    simpa [prefixWord, tailWord_6492531, baseEnd_6492531] using wordTrace_append hprefix tailTrace_6492531
  have hstable : (prefixWord ++ tailWord_6492531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492531).length < 2 ^ (prefixWord ++ tailWord_6492531).sum := by decide
  have hdescent : baseEnd_6492531 < baseStart_6492531 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492548 : List Nat := [2, 3, 2, 1, 1, 2, 1, 4, 7]
def baseStart_6492548 : Nat := 118140960795 + 6492548 * 2 ^ 59
def prefixEnd_6492548 : Nat := 4983230072969 + 3 ^ 40 * 6492548 * 2
def baseEnd_6492548 : Nat := 370421977376374345532369

theorem tailTrace_6492548 : CollatzResearch.WordTrace tailWord_6492548 prefixEnd_6492548 370421977376374345532369 := by
  unfold tailWord_6492548
  simp only [CollatzResearch.WordTrace]
  refine ⟨118401339841307454882167149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157868453121743273176222865 118401339841307454882167149)
  ·
    refine ⟨44400502440490295580812681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118401339841307454882167149 44400502440490295580812681)
    ·
      refine ⟨33300376830367721685609511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44400502440490295580812681 33300376830367721685609511)
      ·
        refine ⟨49950565245551582528414267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33300376830367721685609511 49950565245551582528414267)
        ·
          refine ⟨74925847868327373792621401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49950565245551582528414267 74925847868327373792621401)
          ·
            refine ⟨56194385901245530344466051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74925847868327373792621401 56194385901245530344466051)
            ·
              refine ⟨84291578851868295516699077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56194385901245530344466051 84291578851868295516699077)
              ·
                refine ⟨15804671034725305409381077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84291578851868295516699077 15804671034725305409381077)
                ·
                  refine ⟨370421977376374345532369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15804671034725305409381077 370421977376374345532369)
                  ·
                    rfl

theorem cell23_6492548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_6492548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492548 prefixEnd_6492548 := by exact prefixLift 6492548
  have htrace : WordTrace (prefixWord ++ tailWord_6492548) baseStart_6492548 baseEnd_6492548 := by
    simpa [prefixWord, tailWord_6492548, baseEnd_6492548] using wordTrace_append hprefix tailTrace_6492548
  have hstable : (prefixWord ++ tailWord_6492548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492548).length < 2 ^ (prefixWord ++ tailWord_6492548).sum := by decide
  have hdescent : baseEnd_6492548 < baseStart_6492548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492615 : List Nat := [1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_6492615 : Nat := 118140960795 + 6492615 * 2 ^ 59
def prefixEnd_6492615 : Nat := 4983230072969 + 3 ^ 40 * 6492615 * 2
def baseEnd_6492615 : Nat := 3333832199591220347653513

theorem tailTrace_6492615 : CollatzResearch.WordTrace tailWord_6492615 prefixEnd_6492615 3333832199591220347653513 := by
  unfold tailWord_6492615
  simp only [CollatzResearch.WordTrace]
  refine ⟨236805123373372180207023299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157870082248914786804682199 236805123373372180207023299)
  ·
    refine ⟨355207685060058270310534949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236805123373372180207023299 355207685060058270310534949)
    ·
      refine ⟨66601440948760925683225303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 355207685060058270310534949 66601440948760925683225303)
      ·
        refine ⟨99902161423141388524837955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66601440948760925683225303 99902161423141388524837955)
        ·
          refine ⟨149853242134712082787256933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99902161423141388524837955 149853242134712082787256933)
          ·
            refine ⟨28097482900258515522610675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149853242134712082787256933 28097482900258515522610675)
            ·
              refine ⟨42146224350387773283916013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28097482900258515522610675 42146224350387773283916013)
              ·
                refine ⟨15804834131395414981468505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42146224350387773283916013 15804834131395414981468505)
                ·
                  refine ⟨11853625598546561236101379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15804834131395414981468505 11853625598546561236101379)
                  ·
                    refine ⟨17780438397819841854152069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11853625598546561236101379 17780438397819841854152069)
                    ·
                      refine ⟨3333832199591220347653513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17780438397819841854152069 3333832199591220347653513)
                      ·
                        rfl

theorem cell23_6492615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_6492615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492615 prefixEnd_6492615 := by exact prefixLift 6492615
  have htrace : WordTrace (prefixWord ++ tailWord_6492615) baseStart_6492615 baseEnd_6492615 := by
    simpa [prefixWord, tailWord_6492615, baseEnd_6492615] using wordTrace_append hprefix tailTrace_6492615
  have hstable : (prefixWord ++ tailWord_6492615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492615).length < 2 ^ (prefixWord ++ tailWord_6492615).sum := by decide
  have hdescent : baseEnd_6492615 < baseStart_6492615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492676 : List Nat := [2, 3, 2, 3, 1, 2, 2, 3, 1, 4]
def baseStart_6492676 : Nat := 118140960795 + 6492676 * 2 ^ 59
def prefixEnd_6492676 : Nat := 4983230072969 + 3 ^ 40 * 6492676 * 2
def baseEnd_6492676 : Nat := 1111287840637048202996911

theorem tailTrace_6492676 : CollatzResearch.WordTrace tailWord_6492676 prefixEnd_6492676 1111287840637048202996911 := by
  unfold tailWord_6492676
  simp only [CollatzResearch.WordTrace]
  refine ⟨118403674113075593812496941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157871565484100791749995921 118403674113075593812496941)
  ·
    refine ⟨44401377792403347679686353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118403674113075593812496941 44401377792403347679686353)
    ·
      refine ⟨33301033344302510759764765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44401377792403347679686353 33301033344302510759764765)
      ·
        refine ⟨12487887504113441534911787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33301033344302510759764765 12487887504113441534911787)
        ·
          refine ⟨18731831256170162302367681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12487887504113441534911787 18731831256170162302367681)
          ·
            refine ⟨14048873442127621726775761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18731831256170162302367681 14048873442127621726775761)
            ·
              refine ⟨10536655081595716295081821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14048873442127621726775761 10536655081595716295081821)
              ·
                refine ⟨3951245655598393610655683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10536655081595716295081821 3951245655598393610655683)
                ·
                  refine ⟨5926868483397590415983525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3951245655598393610655683 5926868483397590415983525)
                  ·
                    refine ⟨1111287840637048202996911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5926868483397590415983525 1111287840637048202996911)
                    ·
                      rfl

theorem cell23_6492676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 1, 4].length) (baseStart_6492676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492676 prefixEnd_6492676 := by exact prefixLift 6492676
  have htrace : WordTrace (prefixWord ++ tailWord_6492676) baseStart_6492676 baseEnd_6492676 := by
    simpa [prefixWord, tailWord_6492676, baseEnd_6492676] using wordTrace_append hprefix tailTrace_6492676
  have hstable : (prefixWord ++ tailWord_6492676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492676).length < 2 ^ (prefixWord ++ tailWord_6492676).sum := by decide
  have hdescent : baseEnd_6492676 < baseStart_6492676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492682 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 5, 1, 3]
def baseStart_6492682 : Nat := 118140960795 + 6492682 * 2 ^ 59
def prefixEnd_6492682 : Nat := 4983230072969 + 3 ^ 40 * 6492682 * 2
def baseEnd_6492682 : Nat := 3333866602795071585515705

theorem tailTrace_6492682 : CollatzResearch.WordTrace tailWord_6492682 prefixEnd_6492682 3333866602795071585515705 := by
  unfold tailWord_6492682
  simp only [CollatzResearch.WordTrace]
  refine ⟨59201891766032362662428075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157871711376086300433141533 59201891766032362662428075)
  ·
    refine ⟨88802837649048543993642113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59201891766032362662428075 88802837649048543993642113)
    ·
      refine ⟨66602128236786407995231585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88802837649048543993642113 66602128236786407995231585)
      ·
        refine ⟨49951596177589805996423689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66602128236786407995231585 49951596177589805996423689)
        ·
          refine ⟨37463697133192354497317767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49951596177589805996423689 37463697133192354497317767)
          ·
            refine ⟨56195545699788531745976651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37463697133192354497317767 56195545699788531745976651)
            ·
              refine ⟨84293318549682797618964977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56195545699788531745976651 84293318549682797618964977)
              ·
                refine ⟨63219988912262098214223733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84293318549682797618964977 63219988912262098214223733)
                ·
                  refine ⟨5926873960524571707583475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63219988912262098214223733 5926873960524571707583475)
                  ·
                    refine ⟨8890310940786857561375213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5926873960524571707583475 8890310940786857561375213)
                    ·
                      refine ⟨3333866602795071585515705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8890310940786857561375213 3333866602795071585515705)
                      ·
                        rfl

theorem cell23_6492682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_6492682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492682 prefixEnd_6492682 := by exact prefixLift 6492682
  have htrace : WordTrace (prefixWord ++ tailWord_6492682) baseStart_6492682 baseEnd_6492682 := by
    simpa [prefixWord, tailWord_6492682, baseEnd_6492682] using wordTrace_append hprefix tailTrace_6492682
  have hstable : (prefixWord ++ tailWord_6492682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492682).length < 2 ^ (prefixWord ++ tailWord_6492682).sum := by decide
  have hdescent : baseEnd_6492682 < baseStart_6492682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492692 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_6492692 : Nat := 118140960795 + 6492692 * 2 ^ 59
def prefixEnd_6492692 : Nat := 4983230072969 + 3 ^ 40 * 6492692 * 2
def baseEnd_6492692 : Nat := 3333871737601616546390659

theorem tailTrace_6492692 : CollatzResearch.WordTrace tailWord_6492692 prefixEnd_6492692 3333871737601616546390659 := by
  unfold tailWord_6492692
  simp only [CollatzResearch.WordTrace]
  refine ⟨118403965897046611178788165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157871954529395481571717553 118403965897046611178788165)
  ·
    refine ⟨22200743605696239596022781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118403965897046611178788165 22200743605696239596022781)
    ·
      refine ⟨8325278852136089848508543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22200743605696239596022781 8325278852136089848508543)
      ·
        refine ⟨12487918278204134772762815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8325278852136089848508543 12487918278204134772762815)
        ·
          refine ⟨18731877417306202159144223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12487918278204134772762815 18731877417306202159144223)
          ·
            refine ⟨28097816125959303238716335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18731877417306202159144223 28097816125959303238716335)
            ·
              refine ⟨42146724188938954858074503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28097816125959303238716335 42146724188938954858074503)
              ·
                refine ⟨63220086283408432287111755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42146724188938954858074503 63220086283408432287111755)
                ·
                  refine ⟨94830129425112648430667633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63220086283408432287111755 94830129425112648430667633)
                  ·
                    refine ⟨71122597068834486323000725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94830129425112648430667633 71122597068834486323000725)
                    ·
                      refine ⟨3333871737601616546390659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71122597068834486323000725 3333871737601616546390659)
                      ·
                        rfl

theorem cell23_6492692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_6492692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492692 prefixEnd_6492692 := by exact prefixLift 6492692
  have htrace : WordTrace (prefixWord ++ tailWord_6492692) baseStart_6492692 baseEnd_6492692 := by
    simpa [prefixWord, tailWord_6492692, baseEnd_6492692] using wordTrace_append hprefix tailTrace_6492692
  have hstable : (prefixWord ++ tailWord_6492692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492692).length < 2 ^ (prefixWord ++ tailWord_6492692).sum := by decide
  have hdescent : baseEnd_6492692 < baseStart_6492692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492722 : List Nat := [3, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4]
def baseStart_6492722 : Nat := 118140960795 + 6492722 * 2 ^ 59
def prefixEnd_6492722 : Nat := 4983230072969 + 3 ^ 40 * 6492722 * 2
def baseEnd_6492722 : Nat := 3333887142021251429015521

theorem tailTrace_6492722 : CollatzResearch.WordTrace tailWord_6492722 prefixEnd_6492722 3333887142021251429015521 := by
  unfold tailWord_6492722
  simp only [CollatzResearch.WordTrace]
  refine ⟨59202256495996134370292105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157872683989323024987445613 59202256495996134370292105)
  ·
    refine ⟨44401692371997100777719079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59202256495996134370292105 44401692371997100777719079)
    ·
      refine ⟨66602538557995651166578619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44401692371997100777719079 66602538557995651166578619)
      ·
        refine ⟨99903807836993476749867929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66602538557995651166578619 99903807836993476749867929)
        ·
          refine ⟨74927855877745107562400947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99903807836993476749867929 74927855877745107562400947)
          ·
            refine ⟨112391783816617661343601421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74927855877745107562400947 112391783816617661343601421)
            ·
              refine ⟨42146918931231623003850533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112391783816617661343601421 42146918931231623003850533)
              ·
                refine ⟨7902547299605929313221975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42146918931231623003850533 7902547299605929313221975)
                ·
                  refine ⟨11853820949408893969832963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7902547299605929313221975 11853820949408893969832963)
                  ·
                    refine ⟨17780731424113340954749445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11853820949408893969832963 17780731424113340954749445)
                    ·
                      refine ⟨3333887142021251429015521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17780731424113340954749445 3333887142021251429015521)
                      ·
                        rfl

theorem cell23_6492722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_6492722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492722 prefixEnd_6492722 := by exact prefixLift 6492722
  have htrace : WordTrace (prefixWord ++ tailWord_6492722) baseStart_6492722 baseEnd_6492722 := by
    simpa [prefixWord, tailWord_6492722, baseEnd_6492722] using wordTrace_append hprefix tailTrace_6492722
  have hstable : (prefixWord ++ tailWord_6492722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492722).length < 2 ^ (prefixWord ++ tailWord_6492722).sum := by decide
  have hdescent : baseEnd_6492722 < baseStart_6492722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492725 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 3, 1, 5]
def baseStart_6492725 : Nat := 118140960795 + 6492725 * 2 ^ 59
def prefixEnd_6492725 : Nat := 4983230072969 + 3 ^ 40 * 6492725 * 2
def baseEnd_6492725 : Nat := 3333888682463214917278007

theorem tailTrace_6492725 : CollatzResearch.WordTrace tailWord_6492725 prefixEnd_6492725 3333888682463214917278007 := by
  unfold tailWord_6492725
  simp only [CollatzResearch.WordTrace]
  refine ⟨236809135402973668993527629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157872756935315779329018419 236809135402973668993527629)
  ·
    refine ⟨88803425776115125872572861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236809135402973668993527629 88803425776115125872572861)
    ·
      refine ⟨33301284666043172202214823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88803425776115125872572861 33301284666043172202214823)
      ·
        refine ⟨49951926999064758303322235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33301284666043172202214823 49951926999064758303322235)
        ·
          refine ⟨74927890498597137454983353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49951926999064758303322235 74927890498597137454983353)
          ·
            refine ⟨56195917873947853091237515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74927890498597137454983353 56195917873947853091237515)
            ·
              refine ⟨84293876810921779636856273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56195917873947853091237515 84293876810921779636856273)
              ·
                refine ⟨63220407608191334727642205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84293876810921779636856273 63220407608191334727642205)
                ·
                  refine ⟨23707652853071750522865827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63220407608191334727642205 23707652853071750522865827)
                  ·
                    refine ⟨35561479279607625784298741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23707652853071750522865827 35561479279607625784298741)
                    ·
                      refine ⟨3333888682463214917278007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35561479279607625784298741 3333888682463214917278007)
                      ·
                        rfl

theorem cell23_6492725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_6492725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492725 prefixEnd_6492725 := by exact prefixLift 6492725
  have htrace : WordTrace (prefixWord ++ tailWord_6492725) baseStart_6492725 baseEnd_6492725 := by
    simpa [prefixWord, tailWord_6492725, baseEnd_6492725] using wordTrace_append hprefix tailTrace_6492725
  have hstable : (prefixWord ++ tailWord_6492725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492725).length < 2 ^ (prefixWord ++ tailWord_6492725).sum := by decide
  have hdescent : baseEnd_6492725 < baseStart_6492725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492732 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 4, 4]
def baseStart_6492732 : Nat := 118140960795 + 6492732 * 2 ^ 59
def prefixEnd_6492732 : Nat := 4983230072969 + 3 ^ 40 * 6492732 * 2
def baseEnd_6492732 : Nat := 1111297425609265463296825

theorem tailTrace_6492732 : CollatzResearch.WordTrace tailWord_6492732 prefixEnd_6492732 1111297425609265463296825 := by
  unfold tailWord_6492732
  simp only [CollatzResearch.WordTrace]
  refine ⟨118404695356974154594516225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157872927142632206126021633 118404695356974154594516225)
  ·
    refine ⟨88803521517730615945887169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118404695356974154594516225 88803521517730615945887169)
    ·
      refine ⟨66602641138297961959415377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88803521517730615945887169 66602641138297961959415377)
      ·
        refine ⟨49951980853723471469561533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66602641138297961959415377 49951980853723471469561533)
        ·
          refine ⟨18731992820146301801085575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49951980853723471469561533 18731992820146301801085575)
          ·
            refine ⟨28097989230219452701628363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18731992820146301801085575 28097989230219452701628363)
            ·
              refine ⟨42146983845329179052442545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28097989230219452701628363 42146983845329179052442545)
              ·
                refine ⟨31610237883996884289331909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42146983845329179052442545 31610237883996884289331909)
                ·
                  refine ⟨5926919603249415804249733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31610237883996884289331909 5926919603249415804249733)
                  ·
                    refine ⟨1111297425609265463296825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5926919603249415804249733 1111297425609265463296825)
                    ·
                      rfl

theorem cell23_6492732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_6492732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492732 prefixEnd_6492732 := by exact prefixLift 6492732
  have htrace : WordTrace (prefixWord ++ tailWord_6492732) baseStart_6492732 baseEnd_6492732 := by
    simpa [prefixWord, tailWord_6492732, baseEnd_6492732] using wordTrace_append hprefix tailTrace_6492732
  have hstable : (prefixWord ++ tailWord_6492732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492732).length < 2 ^ (prefixWord ++ tailWord_6492732).sum := by decide
  have hdescent : baseEnd_6492732 < baseStart_6492732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492733 : List Nat := [1, 4, 1, 3, 2, 3, 1, 3, 1, 1, 3]
def baseStart_6492733 : Nat := 118140960795 + 6492733 * 2 ^ 59
def prefixEnd_6492733 : Nat := 4983230072969 + 3 ^ 40 * 6492733 * 2
def baseEnd_6492733 : Nat := 3333892790308450885977971

theorem tailTrace_6492733 : CollatzResearch.WordTrace tailWord_6492733 prefixEnd_6492733 3333892790308450885977971 := by
  unfold tailWord_6492733
  simp only [CollatzResearch.WordTrace]
  refine ⟨236809427186944686359818853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157872951457963124239879235 236809427186944686359818853)
  ·
    refine ⟨44401767597552128692466035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236809427186944686359818853 44401767597552128692466035)
    ·
      refine ⟨66602651396328193038699053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44401767597552128692466035 66602651396328193038699053)
      ·
        refine ⟨24975994273623072389512145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66602651396328193038699053 24975994273623072389512145)
        ·
          refine ⟨18731995705217304292134109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24975994273623072389512145 18731995705217304292134109)
          ·
            refine ⟨7024498389456489109550291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18731995705217304292134109 7024498389456489109550291)
            ·
              refine ⟨10536747584184733664325437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7024498389456489109550291 10536747584184733664325437)
              ·
                refine ⟨3951280344069275124122039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10536747584184733664325437 3951280344069275124122039)
                ·
                  refine ⟨5926920516103912686183059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3951280344069275124122039 5926920516103912686183059)
                  ·
                    refine ⟨8890380774155869029274589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5926920516103912686183059 8890380774155869029274589)
                    ·
                      refine ⟨3333892790308450885977971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8890380774155869029274589 3333892790308450885977971)
                      ·
                        rfl

theorem cell23_6492733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_6492733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492733 prefixEnd_6492733 := by exact prefixLift 6492733
  have htrace : WordTrace (prefixWord ++ tailWord_6492733) baseStart_6492733 baseEnd_6492733 := by
    simpa [prefixWord, tailWord_6492733, baseEnd_6492733] using wordTrace_append hprefix tailTrace_6492733
  have hstable : (prefixWord ++ tailWord_6492733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492733).length < 2 ^ (prefixWord ++ tailWord_6492733).sum := by decide
  have hdescent : baseEnd_6492733 < baseStart_6492733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492735 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 4]
def baseStart_6492735 : Nat := 118140960795 + 6492735 * 2 ^ 59
def prefixEnd_6492735 : Nat := 4983230072969 + 3 ^ 40 * 6492735 * 2
def baseEnd_6492735 : Nat := 3333893817269759878152961

theorem tailTrace_6492735 : CollatzResearch.WordTrace tailWord_6492735 prefixEnd_6492735 3333893817269759878152961 := by
  unfold tailWord_6492735
  simp only [CollatzResearch.WordTrace]
  refine ⟨236809500132937440701391659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157873000088624960467594439 236809500132937440701391659)
  ·
    refine ⟨355214250199406161052087489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236809500132937440701391659 355214250199406161052087489)
    ·
      refine ⟨266410687649554620789065617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355214250199406161052087489 266410687649554620789065617)
      ·
        refine ⟨199808015737165965591799213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266410687649554620789065617 199808015737165965591799213)
        ·
          refine ⟨74928005901437237096924705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199808015737165965591799213 74928005901437237096924705)
          ·
            refine ⟨56196004426077927822693529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74928005901437237096924705 56196004426077927822693529)
            ·
              refine ⟨42147003319558445867020147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56196004426077927822693529 42147003319558445867020147)
              ·
                refine ⟨63220504979337668800530221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42147003319558445867020147 63220504979337668800530221)
                ·
                  refine ⟨23707689367251625800198833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63220504979337668800530221 23707689367251625800198833)
                  ·
                    refine ⟨17780767025438719350149125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23707689367251625800198833 17780767025438719350149125)
                    ·
                      refine ⟨3333893817269759878152961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17780767025438719350149125 3333893817269759878152961)
                      ·
                        rfl

theorem cell23_6492735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_6492735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492735 prefixEnd_6492735 := by exact prefixLift 6492735
  have htrace : WordTrace (prefixWord ++ tailWord_6492735) baseStart_6492735 baseEnd_6492735 := by
    simpa [prefixWord, tailWord_6492735, baseEnd_6492735] using wordTrace_append hprefix tailTrace_6492735
  have hstable : (prefixWord ++ tailWord_6492735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492735).length < 2 ^ (prefixWord ++ tailWord_6492735).sum := by decide
  have hdescent : baseEnd_6492735 < baseStart_6492735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492749 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_6492749 : Nat := 118140960795 + 6492749 * 2 ^ 59
def prefixEnd_6492749 : Nat := 4983230072969 + 3 ^ 40 * 6492749 * 2
def baseEnd_6492749 : Nat := 1111300335332974274459299

theorem tailTrace_6492749 : CollatzResearch.WordTrace tailWord_6492749 prefixEnd_6492749 1111300335332974274459299 := by
  unfold tailWord_6492749
  simp only [CollatzResearch.WordTrace]
  refine ⟨236810010754886721092401301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157873340503257814061600867 236810010754886721092401301)
  ·
    refine ⟨11100469254135315051206311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 236810010754886721092401301 11100469254135315051206311)
    ·
      refine ⟨16650703881202972576809467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11100469254135315051206311 16650703881202972576809467)
      ·
        refine ⟨24976055821804458865214201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16650703881202972576809467 24976055821804458865214201)
        ·
          refine ⟨18732041866353344148910651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24976055821804458865214201 18732041866353344148910651)
          ·
            refine ⟨28098062799530016223365977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18732041866353344148910651 28098062799530016223365977)
            ·
              refine ⟨21073547099647512167524483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28098062799530016223365977 21073547099647512167524483)
              ·
                refine ⟨31610320649471268251286725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21073547099647512167524483 31610320649471268251286725)
                ·
                  refine ⟨5926935121775862797116261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31610320649471268251286725 5926935121775862797116261)
                  ·
                    refine ⟨1111300335332974274459299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5926935121775862797116261 1111300335332974274459299)
                    ·
                      rfl

theorem cell23_6492749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_6492749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492749 prefixEnd_6492749 := by exact prefixLift 6492749
  have htrace : WordTrace (prefixWord ++ tailWord_6492749) baseStart_6492749 baseEnd_6492749 := by
    simpa [prefixWord, tailWord_6492749, baseEnd_6492749] using wordTrace_append hprefix tailTrace_6492749
  have hstable : (prefixWord ++ tailWord_6492749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492749).length < 2 ^ (prefixWord ++ tailWord_6492749).sum := by decide
  have hdescent : baseEnd_6492749 < baseStart_6492749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492756 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 3, 2, 2]
def baseStart_6492756 : Nat := 118140960795 + 6492756 * 2 ^ 59
def prefixEnd_6492756 : Nat := 4983230072969 + 3 ^ 40 * 6492756 * 2
def baseEnd_6492756 : Nat := 3333904600363504295990365

theorem tailTrace_6492756 : CollatzResearch.WordTrace tailWord_6492756 prefixEnd_6492756 3333904600363504295990365 := by
  unfold tailWord_6492756
  simp only [CollatzResearch.WordTrace]
  refine ⟨118405133032930680643953061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157873510710574240858604081 118405133032930680643953061)
  ·
    refine ⟨22200962443674502620741199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118405133032930680643953061 22200962443674502620741199)
    ·
      refine ⟨33301443665511753931111799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22200962443674502620741199 33301443665511753931111799)
      ·
        refine ⟨49952165498267630896667699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33301443665511753931111799 49952165498267630896667699)
        ·
          refine ⟨74928248247401446345001549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49952165498267630896667699 74928248247401446345001549)
          ·
            refine ⟨28098093092775542379375581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74928248247401446345001549 28098093092775542379375581)
            ·
              refine ⟨10536784909790828392265843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28098093092775542379375581 10536784909790828392265843)
              ·
                refine ⟨15805177364686242588398765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10536784909790828392265843 15805177364686242588398765)
                ·
                  refine ⟨5926941511757340970649537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15805177364686242588398765 5926941511757340970649537)
                  ·
                    refine ⟨4445206133818005727987153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5926941511757340970649537 4445206133818005727987153)
                    ·
                      refine ⟨3333904600363504295990365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4445206133818005727987153 3333904600363504295990365)
                      ·
                        rfl

theorem cell23_6492756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_6492756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492756 prefixEnd_6492756 := by exact prefixLift 6492756
  have htrace : WordTrace (prefixWord ++ tailWord_6492756) baseStart_6492756 baseEnd_6492756 := by
    simpa [prefixWord, tailWord_6492756, baseEnd_6492756] using wordTrace_append hprefix tailTrace_6492756
  have hstable : (prefixWord ++ tailWord_6492756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492756).length < 2 ^ (prefixWord ++ tailWord_6492756).sum := by decide
  have hdescent : baseEnd_6492756 < baseStart_6492756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492772 : List Nat := [2, 3, 1, 1, 2, 2, 2, 3, 1, 3, 3]
def baseStart_6492772 : Nat := 118140960795 + 6492772 * 2 ^ 59
def prefixEnd_6492772 : Nat := 4983230072969 + 3 ^ 40 * 6492772 * 2
def baseEnd_6492772 : Nat := 3333912816053976233390291

theorem tailTrace_6492772 : CollatzResearch.WordTrace tailWord_6492772 prefixEnd_6492772 3333912816053976233390291 := by
  unfold tailWord_6492772
  simp only [CollatzResearch.WordTrace]
  refine ⟨118405424816901698010244285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157873899755868930680325713 118405424816901698010244285)
  ·
    refine ⟨44402034306338136753841607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118405424816901698010244285 44402034306338136753841607)
    ·
      refine ⟨66603051459507205130762411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44402034306338136753841607 66603051459507205130762411)
      ·
        refine ⟨99904577189260807696143617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66603051459507205130762411 99904577189260807696143617)
        ·
          refine ⟨74928432891945605772107713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99904577189260807696143617 74928432891945605772107713)
          ·
            refine ⟨56196324668959204329080785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74928432891945605772107713 56196324668959204329080785)
            ·
              refine ⟨42147243501719403246810589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56196324668959204329080785 42147243501719403246810589)
              ·
                refine ⟨15805216313144776217553971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42147243501719403246810589 15805216313144776217553971)
                ·
                  refine ⟨23707824469717164326330957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15805216313144776217553971 23707824469717164326330957)
                  ·
                    refine ⟨8890434176143936622374109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23707824469717164326330957 8890434176143936622374109)
                    ·
                      refine ⟨3333912816053976233390291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8890434176143936622374109 3333912816053976233390291)
                      ·
                        rfl

theorem cell23_6492772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_6492772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492772 prefixEnd_6492772 := by exact prefixLift 6492772
  have htrace : WordTrace (prefixWord ++ tailWord_6492772) baseStart_6492772 baseEnd_6492772 := by
    simpa [prefixWord, tailWord_6492772, baseEnd_6492772] using wordTrace_append hprefix tailTrace_6492772
  have hstable : (prefixWord ++ tailWord_6492772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492772).length < 2 ^ (prefixWord ++ tailWord_6492772).sum := by decide
  have hdescent : baseEnd_6492772 < baseStart_6492772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492829 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 1, 4, 2]
def baseStart_6492829 : Nat := 118140960795 + 6492829 * 2 ^ 59
def prefixEnd_6492829 : Nat := 4983230072969 + 3 ^ 40 * 6492829 * 2
def baseEnd_6492829 : Nat := 3333942084451282510377529

theorem tailTrace_6492829 : CollatzResearch.WordTrace tailWord_6492829 prefixEnd_6492829 3333942084451282510377529 := by
  unfold tailWord_6492829
  simp only [CollatzResearch.WordTrace]
  refine ⟨236812928594596894755313541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157875285729731263170209027 236812928594596894755313541)
  ·
    refine ⟨44402424111486917766621289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236812928594596894755313541 44402424111486917766621289)
    ·
      refine ⟨33301818083615188324965967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44402424111486917766621289 33301818083615188324965967)
      ·
        refine ⟨49952727125422782487448951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33301818083615188324965967 49952727125422782487448951)
        ·
          refine ⟨74929090688134173731173427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49952727125422782487448951 74929090688134173731173427)
          ·
            refine ⟨112393636032201260596760141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74929090688134173731173427 112393636032201260596760141)
            ·
              refine ⟨42147613512075472723785053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112393636032201260596760141 42147613512075472723785053)
              ·
                refine ⟨15805355067028302271419395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42147613512075472723785053 15805355067028302271419395)
                ·
                  refine ⟨23708032600542453407129093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15805355067028302271419395 23708032600542453407129093)
                  ·
                    refine ⟨4445256112601710013836705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23708032600542453407129093 4445256112601710013836705)
                    ·
                      refine ⟨3333942084451282510377529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4445256112601710013836705 3333942084451282510377529)
                      ·
                        rfl

theorem cell23_6492829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_6492829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492829 prefixEnd_6492829 := by exact prefixLift 6492829
  have htrace : WordTrace (prefixWord ++ tailWord_6492829) baseStart_6492829 baseEnd_6492829 := by
    simpa [prefixWord, tailWord_6492829, baseEnd_6492829] using wordTrace_append hprefix tailTrace_6492829
  have hstable : (prefixWord ++ tailWord_6492829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492829).length < 2 ^ (prefixWord ++ tailWord_6492829).sum := by decide
  have hdescent : baseEnd_6492829 < baseStart_6492829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492863 : List Nat := [1, 1, 2, 2, 2, 6, 1, 2, 2, 2, 2]
def baseStart_6492863 : Nat := 118140960795 + 6492863 * 2 ^ 59
def prefixEnd_6492863 : Nat := 4983230072969 + 3 ^ 40 * 6492863 * 2
def baseEnd_6492863 : Nat := 3333959542793535377352373

theorem tailTrace_6492863 : CollatzResearch.WordTrace tailWord_6492863 prefixEnd_6492863 3333959542793535377352373 := by
  unfold tailWord_6492863
  simp only [CollatzResearch.WordTrace]
  refine ⟨236814168676473718562051243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157876112450982479041367495 236814168676473718562051243)
  ·
    refine ⟨355221253014710577843076865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236814168676473718562051243 355221253014710577843076865)
    ·
      refine ⟨266415939761032933382307649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355221253014710577843076865 266415939761032933382307649)
      ·
        refine ⟨199811954820774700036730737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266415939761032933382307649 199811954820774700036730737)
        ·
          refine ⟨149858966115581025027548053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199811954820774700036730737 149858966115581025027548053)
          ·
            refine ⟨7024639036667860548166315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 149858966115581025027548053 7024639036667860548166315)
            ·
              refine ⟨10536958555001790822249473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7024639036667860548166315 10536958555001790822249473)
              ·
                refine ⟨7902718916251343116687105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10536958555001790822249473 7902718916251343116687105)
                ·
                  refine ⟨5927039187188507337515329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7902718916251343116687105 5927039187188507337515329)
                  ·
                    refine ⟨4445279390391380503136497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5927039187188507337515329 4445279390391380503136497)
                    ·
                      refine ⟨3333959542793535377352373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4445279390391380503136497 3333959542793535377352373)
                      ·
                        rfl

theorem cell23_6492863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 2, 2].length) (baseStart_6492863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492863 prefixEnd_6492863 := by exact prefixLift 6492863
  have htrace : WordTrace (prefixWord ++ tailWord_6492863) baseStart_6492863 baseEnd_6492863 := by
    simpa [prefixWord, tailWord_6492863, baseEnd_6492863] using wordTrace_append hprefix tailTrace_6492863
  have hstable : (prefixWord ++ tailWord_6492863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492863).length < 2 ^ (prefixWord ++ tailWord_6492863).sum := by decide
  have hdescent : baseEnd_6492863 < baseStart_6492863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492956 : List Nat := [2, 2, 3, 1, 1, 4, 2, 1, 2, 2, 3]
def baseStart_6492956 : Nat := 118140960795 + 6492956 * 2 ^ 59
def prefixEnd_6492956 : Nat := 4983230072969 + 3 ^ 40 * 6492956 * 2
def baseEnd_6492956 : Nat := 3334007296494403513489445

theorem tailTrace_6492956 : CollatzResearch.WordTrace tailWord_6492956 prefixEnd_6492956 3334007296494403513489445 := by
  unfold tailWord_6492956
  simp only [CollatzResearch.WordTrace]
  refine ⟨118408780332568397722593361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157878373776757863630124481 118408780332568397722593361)
  ·
    refine ⟨88806585249426298291945021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118408780332568397722593361 88806585249426298291945021)
    ·
      refine ⟨33302469468534861859479383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88806585249426298291945021 33302469468534861859479383)
      ·
        refine ⟨49953704202802292789219075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33302469468534861859479383 49953704202802292789219075)
        ·
          refine ⟨74930556304203439183828613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49953704202802292789219075 74930556304203439183828613)
          ·
            refine ⟨14049479307038144846967865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74930556304203439183828613 14049479307038144846967865)
            ·
              refine ⟨10537109480278608635225899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14049479307038144846967865 10537109480278608635225899)
              ·
                refine ⟨15805664220417912952838849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10537109480278608635225899 15805664220417912952838849)
                ·
                  refine ⟨11854248165313434714629137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15805664220417912952838849 11854248165313434714629137)
                  ·
                    refine ⟨8890686123985076035971853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11854248165313434714629137 8890686123985076035971853)
                    ·
                      refine ⟨3334007296494403513489445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8890686123985076035971853 3334007296494403513489445)
                      ·
                        rfl

theorem cell23_6492956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_6492956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492956 prefixEnd_6492956 := by exact prefixLift 6492956
  have htrace : WordTrace (prefixWord ++ tailWord_6492956) baseStart_6492956 baseEnd_6492956 := by
    simpa [prefixWord, tailWord_6492956, baseEnd_6492956] using wordTrace_append hprefix tailTrace_6492956
  have hstable : (prefixWord ++ tailWord_6492956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492956).length < 2 ^ (prefixWord ++ tailWord_6492956).sum := by decide
  have hdescent : baseEnd_6492956 < baseStart_6492956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492969 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 5, 1, 3]
def baseStart_6492969 : Nat := 118140960795 + 6492969 * 2 ^ 59
def prefixEnd_6492969 : Nat := 4983230072969 + 3 ^ 40 * 6492969 * 2
def baseEnd_6492969 : Nat := 3334013971742911962626885

theorem tailTrace_6492969 : CollatzResearch.WordTrace tailWord_6492969 prefixEnd_6492969 3334013971742911962626885 := by
  unfold tailWord_6492969
  simp only [CollatzResearch.WordTrace]
  refine ⟨236818034814089698665409961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157878689876059799110273307 236818034814089698665409961)
  ·
    refine ⟨177613526110567273999057471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236818034814089698665409961 177613526110567273999057471)
    ·
      refine ⟨266420289165850910998586207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177613526110567273999057471 266420289165850910998586207)
      ·
        refine ⟨399630433748776366497879311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266420289165850910998586207 399630433748776366497879311)
        ·
          refine ⟨599445650623164549746818967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399630433748776366497879311 599445650623164549746818967)
          ·
            refine ⟨899168475934746824620228451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599445650623164549746818967 899168475934746824620228451)
            ·
              refine ⟨1348752713902120236930342677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899168475934746824620228451 1348752713902120236930342677)
              ·
                refine ⟨63222783464161886106109813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1348752713902120236930342677 63222783464161886106109813)
                ·
                  refine ⟨5927135949765176822447795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63222783464161886106109813 5927135949765176822447795)
                  ·
                    refine ⟨8890703924647765233671693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5927135949765176822447795 8890703924647765233671693)
                    ·
                      refine ⟨3334013971742911962626885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8890703924647765233671693 3334013971742911962626885)
                      ·
                        rfl

theorem cell23_6492969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 1, 3].length) (baseStart_6492969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492969 prefixEnd_6492969 := by exact prefixLift 6492969
  have htrace : WordTrace (prefixWord ++ tailWord_6492969) baseStart_6492969 baseEnd_6492969 := by
    simpa [prefixWord, tailWord_6492969, baseEnd_6492969] using wordTrace_append hprefix tailTrace_6492969
  have hstable : (prefixWord ++ tailWord_6492969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492969).length < 2 ^ (prefixWord ++ tailWord_6492969).sum := by decide
  have hdescent : baseEnd_6492969 < baseStart_6492969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6492980 : List Nat := [2, 5, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_6492980 : Nat := 118140960795 + 6492980 * 2 ^ 59
def prefixEnd_6492980 : Nat := 4983230072969 + 3 ^ 40 * 6492980 * 2
def baseEnd_6492980 : Nat := 1111339873343370473196445

theorem tailTrace_6492980 : CollatzResearch.WordTrace tailWord_6492980 prefixEnd_6492980 1111339873343370473196445 := by
  unfold tailWord_6492980
  simp only [CollatzResearch.WordTrace]
  refine ⟨118409218008524923772030197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157878957344699898362706929 118409218008524923772030197)
  ·
    refine ⟨11100864188299211603627831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118409218008524923772030197 11100864188299211603627831)
    ·
      refine ⟨16651296282448817405441747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11100864188299211603627831 16651296282448817405441747)
      ·
        refine ⟨24976944423673226108162621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16651296282448817405441747 24976944423673226108162621)
        ·
          refine ⟨9366354158877459790560983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24976944423673226108162621 9366354158877459790560983)
          ·
            refine ⟨14049531238316189685841475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9366354158877459790560983 14049531238316189685841475)
            ·
              refine ⟨21074296857474284528762213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14049531238316189685841475 21074296857474284528762213)
              ·
                refine ⟨3951430660776428349142915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21074296857474284528762213 3951430660776428349142915)
                ·
                  refine ⟨5927145991164642523714373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3951430660776428349142915 5927145991164642523714373)
                  ·
                    refine ⟨1111339873343370473196445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5927145991164642523714373 1111339873343370473196445)
                    ·
                      rfl

theorem cell23_6492980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_6492980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6492980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6492980 prefixEnd_6492980 := by exact prefixLift 6492980
  have htrace : WordTrace (prefixWord ++ tailWord_6492980) baseStart_6492980 baseEnd_6492980 := by
    simpa [prefixWord, tailWord_6492980, baseEnd_6492980] using wordTrace_append hprefix tailTrace_6492980
  have hstable : (prefixWord ++ tailWord_6492980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6492980).length < 2 ^ (prefixWord ++ tailWord_6492980).sum := by decide
  have hdescent : baseEnd_6492980 < baseStart_6492980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6492980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493020 : List Nat := [2, 2, 4, 2, 1, 1, 1, 5, 1, 1, 3]
def baseStart_6493020 : Nat := 118140960795 + 6493020 * 2 ^ 59
def prefixEnd_6493020 : Nat := 4983230072969 + 3 ^ 40 * 6493020 * 2
def baseEnd_6493020 : Nat := 3334040159256291263089151

theorem tailTrace_6493020 : CollatzResearch.WordTrace tailWord_6493020 prefixEnd_6493020 3334040159256291263089151 := by
  unfold tailWord_6493020
  simp only [CollatzResearch.WordTrace]
  refine ⟨118409947468452467187758257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157879929957936622917011009 118409947468452467187758257)
  ·
    refine ⟨88807460601339350390818693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118409947468452467187758257 88807460601339350390818693)
    ·
      refine ⟨16651398862751128198278505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 88807460601339350390818693 16651398862751128198278505)
      ·
        refine ⟨12488549147063346148708879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16651398862751128198278505 12488549147063346148708879)
        ·
          refine ⟨18732823720595019223063319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12488549147063346148708879 18732823720595019223063319)
          ·
            refine ⟨28099235580892528834594979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18732823720595019223063319 28099235580892528834594979)
            ·
              refine ⟨42148853371338793251892469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28099235580892528834594979 42148853371338793251892469)
              ·
                refine ⟨3951455003563011867364919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42148853371338793251892469 3951455003563011867364919)
                ·
                  refine ⟨5927182505344517801047379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3951455003563011867364919 5927182505344517801047379)
                  ·
                    refine ⟨8890773758016776701571069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5927182505344517801047379 8890773758016776701571069)
                    ·
                      refine ⟨3334040159256291263089151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8890773758016776701571069 3334040159256291263089151)
                      ·
                        rfl

theorem cell23_6493020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_6493020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493020 prefixEnd_6493020 := by exact prefixLift 6493020
  have htrace : WordTrace (prefixWord ++ tailWord_6493020) baseStart_6493020 baseEnd_6493020 := by
    simpa [prefixWord, tailWord_6493020, baseEnd_6493020] using wordTrace_append hprefix tailTrace_6493020
  have hstable : (prefixWord ++ tailWord_6493020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493020).length < 2 ^ (prefixWord ++ tailWord_6493020).sum := by decide
  have hdescent : baseEnd_6493020 < baseStart_6493020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493046 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_6493046 : Nat := 118140960795 + 6493046 * 2 ^ 59
def prefixEnd_6493046 : Nat := 4983230072969 + 3 ^ 40 * 6493046 * 2
def baseEnd_6493046 : Nat := 3334053509753308161364031

theorem tailTrace_6493046 : CollatzResearch.WordTrace tailWord_6493046 prefixEnd_6493046 3334053509753308161364031 := by
  unfold tailWord_6493046
  simp only [CollatzResearch.WordTrace]
  refine ⟨14801302702175671300997687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157880562156540493877308661 14801302702175671300997687)
  ·
    refine ⟨22201954053263506951496531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14801302702175671300997687 22201954053263506951496531)
    ·
      refine ⟨33302931079895260427244797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22201954053263506951496531 33302931079895260427244797)
      ·
        refine ⟨12488599154960722660216799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33302931079895260427244797 12488599154960722660216799)
        ·
          refine ⟨18732898732441083990325199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12488599154960722660216799 18732898732441083990325199)
          ·
            refine ⟨28099348098661625985487799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18732898732441083990325199 28099348098661625985487799)
            ·
              refine ⟨42149022147992438978231699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28099348098661625985487799 42149022147992438978231699)
              ·
                refine ⟨63223533221988658467347549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42149022147992438978231699 63223533221988658467347549)
                ·
                  refine ⟨23708824958245746925255331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63223533221988658467347549 23708824958245746925255331)
                  ·
                    refine ⟨35563237437368620387882997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23708824958245746925255331 35563237437368620387882997)
                    ·
                      refine ⟨3334053509753308161364031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35563237437368620387882997 3334053509753308161364031)
                      ·
                        rfl

theorem cell23_6493046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_6493046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493046 prefixEnd_6493046 := by exact prefixLift 6493046
  have htrace : WordTrace (prefixWord ++ tailWord_6493046) baseStart_6493046 baseEnd_6493046 := by
    simpa [prefixWord, tailWord_6493046, baseEnd_6493046] using wordTrace_append hprefix tailTrace_6493046
  have hstable : (prefixWord ++ tailWord_6493046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493046).length < 2 ^ (prefixWord ++ tailWord_6493046).sum := by decide
  have hdescent : baseEnd_6493046 < baseStart_6493046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493063 : List Nat := [1, 1, 4, 2, 3, 2, 2, 2, 1, 2, 3]
def baseStart_6493063 : Nat := 118140960795 + 6493063 * 2 ^ 59
def prefixEnd_6493063 : Nat := 4983230072969 + 3 ^ 40 * 6493063 * 2
def baseEnd_6493063 : Nat := 3334062238924434594851453

theorem tailTrace_6493063 : CollatzResearch.WordTrace tailWord_6493063 prefixEnd_6493063 3334062238924434594851453 := by
  unfold tailWord_6493063
  simp only [CollatzResearch.WordTrace]
  refine ⟨236821463275749152719331843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157880975517166101812887895 236821463275749152719331843)
  ·
    refine ⟨355232194913623729078997765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236821463275749152719331843 355232194913623729078997765)
    ·
      refine ⟨66606036546304449202312081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 355232194913623729078997765 66606036546304449202312081)
      ·
        refine ⟨49954527409728336901734061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66606036546304449202312081 49954527409728336901734061)
        ·
          refine ⟨18732947778648126338150273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49954527409728336901734061 18732947778648126338150273)
          ·
            refine ⟨14049710833986094753612705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18732947778648126338150273 14049710833986094753612705)
            ·
              refine ⟨10537283125489571065209529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14049710833986094753612705 10537283125489571065209529)
              ·
                refine ⟨7902962344117178298907147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10537283125489571065209529 7902962344117178298907147)
                ·
                  refine ⟨11854443516175767448360721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7902962344117178298907147 11854443516175767448360721)
                  ·
                    refine ⟨8890832637131825586270541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11854443516175767448360721 8890832637131825586270541)
                    ·
                      refine ⟨3334062238924434594851453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8890832637131825586270541 3334062238924434594851453)
                      ·
                        rfl

theorem cell23_6493063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_6493063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493063 prefixEnd_6493063 := by exact prefixLift 6493063
  have htrace : WordTrace (prefixWord ++ tailWord_6493063) baseStart_6493063 baseEnd_6493063 := by
    simpa [prefixWord, tailWord_6493063, baseEnd_6493063] using wordTrace_append hprefix tailTrace_6493063
  have hstable : (prefixWord ++ tailWord_6493063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493063).length < 2 ^ (prefixWord ++ tailWord_6493063).sum := by decide
  have hdescent : baseEnd_6493063 < baseStart_6493063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493066 : List Nat := [3, 1, 2, 4, 1, 1, 4, 7]
def baseStart_6493066 : Nat := 118140960795 + 6493066 * 2 ^ 59
def prefixEnd_6493066 : Nat := 4983230072969 + 3 ^ 40 * 6493066 * 2
def baseEnd_6493066 : Nat := 123483843680236966041257

theorem tailTrace_6493066 : CollatzResearch.WordTrace tailWord_6493066 prefixEnd_6493066 123483843680236966041257 := by
  unfold tailWord_6493066
  simp only [CollatzResearch.WordTrace]
  refine ⟨59205393173684571057922763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157881048463158856154460701 59205393173684571057922763)
  ·
    refine ⟨88808089760526856586884145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59205393173684571057922763 88808089760526856586884145)
    ·
      refine ⟨66606067320395142440163109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88808089760526856586884145 66606067320395142440163109)
      ·
        refine ⟨12488637622574089207530583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66606067320395142440163109 12488637622574089207530583)
        ·
          refine ⟨18732956433861133811295875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12488637622574089207530583 18732956433861133811295875)
          ·
            refine ⟨28099434650791700716943813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18732956433861133811295875 28099434650791700716943813)
            ·
              refine ⟨5268643997023443884426965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28099434650791700716943813 5268643997023443884426965)
              ·
                refine ⟨123483843680236966041257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5268643997023443884426965 123483843680236966041257)
                ·
                  rfl

theorem cell23_6493066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 7].length) (baseStart_6493066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493066 prefixEnd_6493066 := by exact prefixLift 6493066
  have htrace : WordTrace (prefixWord ++ tailWord_6493066) baseStart_6493066 baseEnd_6493066 := by
    simpa [prefixWord, tailWord_6493066, baseEnd_6493066] using wordTrace_append hprefix tailTrace_6493066
  have hstable : (prefixWord ++ tailWord_6493066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493066).length < 2 ^ (prefixWord ++ tailWord_6493066).sum := by decide
  have hdescent : baseEnd_6493066 < baseStart_6493066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493072 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 7]
def baseStart_6493072 : Nat := 118140960795 + 6493072 * 2 ^ 59
def prefixEnd_6493072 : Nat := 4983230072969 + 3 ^ 40 * 6493072 * 2
def baseEnd_6493072 : Nat := 3334066860250325059638911

theorem tailTrace_6493072 : CollatzResearch.WordTrace tailWord_6493072 prefixEnd_6493072 3334066860250325059638911 := by
  unfold tailWord_6493072
  simp only [CollatzResearch.WordTrace]
  refine ⟨118410895766358273628204735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157881194355144364837606313 118410895766358273628204735)
  ·
    refine ⟨177616343649537410442307103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118410895766358273628204735 177616343649537410442307103)
    ·
      refine ⟨266424515474306115663460655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177616343649537410442307103 266424515474306115663460655)
      ·
        refine ⟨399636773211459173495190983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266424515474306115663460655 399636773211459173495190983)
        ·
          refine ⟨599455159817188760242786475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399636773211459173495190983 599455159817188760242786475)
          ·
            refine ⟨899182739725783140364179713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599455159817188760242786475 899182739725783140364179713)
            ·
              refine ⟨674387054794337355273134785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899182739725783140364179713 674387054794337355273134785)
              ·
                refine ⟨505790291095753016454851089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674387054794337355273134785 505790291095753016454851089)
                ·
                  refine ⟨379342718321814762341138317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505790291095753016454851089 379342718321814762341138317)
                  ·
                    refine ⟨142253519370680535877926869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379342718321814762341138317 142253519370680535877926869)
                    ·
                      refine ⟨3334066860250325059638911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142253519370680535877926869 3334066860250325059638911)
                      ·
                        rfl

theorem cell23_6493072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_6493072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493072 prefixEnd_6493072 := by exact prefixLift 6493072
  have htrace : WordTrace (prefixWord ++ tailWord_6493072) baseStart_6493072 baseEnd_6493072 := by
    simpa [prefixWord, tailWord_6493072, baseEnd_6493072] using wordTrace_append hprefix tailTrace_6493072
  have hstable : (prefixWord ++ tailWord_6493072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493072).length < 2 ^ (prefixWord ++ tailWord_6493072).sum := by decide
  have hdescent : baseEnd_6493072 < baseStart_6493072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493076 : List Nat := [2, 4, 2, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_6493076 : Nat := 118140960795 + 6493076 * 2 ^ 59
def prefixEnd_6493076 : Nat := 4983230072969 + 3 ^ 40 * 6493076 * 2
def baseEnd_6493076 : Nat := 3334068914172943043988893

theorem tailTrace_6493076 : CollatzResearch.WordTrace tailWord_6493076 prefixEnd_6493076 3334068914172943043988893 := by
  unfold tailWord_6493076
  simp only [CollatzResearch.WordTrace]
  refine ⟨118410968712351027969777541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157881291616468037293036721 118410968712351027969777541)
  ·
    refine ⟨22202056633565817744333289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 118410968712351027969777541 22202056633565817744333289)
    ·
      refine ⟨16651542475174363308249967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22202056633565817744333289 16651542475174363308249967)
      ·
        refine ⟨24977313712761544962374951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16651542475174363308249967 24977313712761544962374951)
        ·
          refine ⟨37465970569142317443562427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24977313712761544962374951 37465970569142317443562427)
          ·
            refine ⟨56198955853713476165343641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37465970569142317443562427 56198955853713476165343641)
            ·
              refine ⟨42149216890285107124007731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56198955853713476165343641 42149216890285107124007731)
              ·
                refine ⟨63223825335427660686011597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42149216890285107124007731 63223825335427660686011597)
                ·
                  refine ⟨23708934500785372757254349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63223825335427660686011597 23708934500785372757254349)
                  ·
                    refine ⟨8890850437794514783970381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23708934500785372757254349 8890850437794514783970381)
                    ·
                      refine ⟨3334068914172943043988893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8890850437794514783970381 3334068914172943043988893)
                      ·
                        rfl

theorem cell23_6493076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_6493076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493076 prefixEnd_6493076 := by exact prefixLift 6493076
  have htrace : WordTrace (prefixWord ++ tailWord_6493076) baseStart_6493076 baseEnd_6493076 := by
    simpa [prefixWord, tailWord_6493076, baseEnd_6493076] using wordTrace_append hprefix tailTrace_6493076
  have hstable : (prefixWord ++ tailWord_6493076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493076).length < 2 ^ (prefixWord ++ tailWord_6493076).sum := by decide
  have hdescent : baseEnd_6493076 < baseStart_6493076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493077 : List Nat := [1, 3, 2, 1, 1, 6, 1, 3, 1, 2, 2]
def baseStart_6493077 : Nat := 118140960795 + 6493077 * 2 ^ 59
def prefixEnd_6493077 : Nat := 4983230072969 + 3 ^ 40 * 6493077 * 2
def baseEnd_6493077 : Nat := 3334069427653597540076389

theorem tailTrace_6493077 : CollatzResearch.WordTrace tailWord_6493077 prefixEnd_6493077 3334069427653597540076389 := by
  unfold tailWord_6493077
  simp only [CollatzResearch.WordTrace]
  refine ⟨236821973897698433110341485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157881315931798955406894323 236821973897698433110341485)
  ·
    refine ⟨88808240211636912416378057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236821973897698433110341485 88808240211636912416378057)
    ·
      refine ⟨66606180158727684312283543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88808240211636912416378057 66606180158727684312283543)
      ·
        refine ⟨99909270238091526468425315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66606180158727684312283543 99909270238091526468425315)
        ·
          refine ⟨149863905357137289702637973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99909270238091526468425315 149863905357137289702637973)
          ·
            refine ⟨7024870563615810454811155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 149863905357137289702637973 7024870563615810454811155)
            ·
              refine ⟨10537305845423715682216733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7024870563615810454811155 10537305845423715682216733)
              ·
                refine ⟨3951489692033893380831275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10537305845423715682216733 3951489692033893380831275)
                ·
                  refine ⟨5927234538050840071246913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3951489692033893380831275 5927234538050840071246913)
                  ·
                    refine ⟨4445425903538130053435185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5927234538050840071246913 4445425903538130053435185)
                    ·
                      refine ⟨3334069427653597540076389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4445425903538130053435185 3334069427653597540076389)
                      ·
                        rfl

theorem cell23_6493077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_6493077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493077 prefixEnd_6493077 := by exact prefixLift 6493077
  have htrace : WordTrace (prefixWord ++ tailWord_6493077) baseStart_6493077 baseEnd_6493077 := by
    simpa [prefixWord, tailWord_6493077, baseEnd_6493077] using wordTrace_append hprefix tailTrace_6493077
  have hstable : (prefixWord ++ tailWord_6493077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493077).length < 2 ^ (prefixWord ++ tailWord_6493077).sum := by decide
  have hdescent : baseEnd_6493077 < baseStart_6493077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493109 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 1, 8]
def baseStart_6493109 : Nat := 118140960795 + 6493109 * 2 ^ 59
def prefixEnd_6493109 : Nat := 4983230072969 + 3 ^ 40 * 6493109 * 2
def baseEnd_6493109 : Nat := 1111361953011513804958747

theorem tailTrace_6493109 : CollatzResearch.WordTrace tailWord_6493109 prefixEnd_6493109 1111361953011513804958747 := by
  unfold tailWord_6493109
  simp only [CollatzResearch.WordTrace]
  refine ⟨236823141033582502575506381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157882094022388335050337587 236823141033582502575506381)
  ·
    refine ⟨88808677887593438465814893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236823141033582502575506381 88808677887593438465814893)
    ·
      refine ⟨33303254207847539424680585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88808677887593438465814893 33303254207847539424680585)
      ·
        refine ⟨24977440655885654568510439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33303254207847539424680585 24977440655885654568510439)
        ·
          refine ⟨37466160983828481852765659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24977440655885654568510439 37466160983828481852765659)
          ·
            refine ⟨56199241475742722779148489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37466160983828481852765659 56199241475742722779148489)
            ·
              refine ⟨42149431106807042084361367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56199241475742722779148489 42149431106807042084361367)
              ·
                refine ⟨63224146660210563126542051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42149431106807042084361367 63224146660210563126542051)
                ·
                  refine ⟨94836219990315844689813077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63224146660210563126542051 94836219990315844689813077)
                  ·
                    refine ⟨1111361953011513804958747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 94836219990315844689813077 1111361953011513804958747)
                    ·
                      rfl

theorem cell23_6493109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_6493109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493109 prefixEnd_6493109 := by exact prefixLift 6493109
  have htrace : WordTrace (prefixWord ++ tailWord_6493109) baseStart_6493109 baseEnd_6493109 := by
    simpa [prefixWord, tailWord_6493109, baseEnd_6493109] using wordTrace_append hprefix tailTrace_6493109
  have hstable : (prefixWord ++ tailWord_6493109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493109).length < 2 ^ (prefixWord ++ tailWord_6493109).sum := by decide
  have hdescent : baseEnd_6493109 < baseStart_6493109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493119 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 3]
def baseStart_6493119 : Nat := 118140960795 + 6493119 * 2 ^ 59
def prefixEnd_6493119 : Nat := 4983230072969 + 3 ^ 40 * 6493119 * 2
def baseEnd_6493119 : Nat := 3334090993841086375751195

theorem tailTrace_6493119 : CollatzResearch.WordTrace tailWord_6493119 prefixEnd_6493119 3334090993841086375751195 := by
  unfold tailWord_6493119
  simp only [CollatzResearch.WordTrace]
  refine ⟨236823505763546274283370411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157882337175697516188913607 236823505763546274283370411)
  ·
    refine ⟨355235258645319411425055617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236823505763546274283370411 355235258645319411425055617)
    ·
      refine ⟨266426443983989558568791713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355235258645319411425055617 266426443983989558568791713)
      ·
        refine ⟨199819832987992168926593785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266426443983989558568791713 199819832987992168926593785)
        ·
          refine ⟨149864874740994126694945339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199819832987992168926593785 149864874740994126694945339)
          ·
            refine ⟨224797312111491190042418009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149864874740994126694945339 224797312111491190042418009)
            ·
              refine ⟨168597984083618392531813507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224797312111491190042418009 168597984083618392531813507)
              ·
                refine ⟨252896976125427588797720261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168597984083618392531813507 252896976125427588797720261)
                ·
                  refine ⟨47418183023517672899572549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252896976125427588797720261 47418183023517672899572549)
                  ·
                    refine ⟨8890909316909563668669853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47418183023517672899572549 8890909316909563668669853)
                    ·
                      refine ⟨3334090993841086375751195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8890909316909563668669853 3334090993841086375751195)
                      ·
                        rfl

theorem cell23_6493119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 3].length) (baseStart_6493119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493119 prefixEnd_6493119 := by exact prefixLift 6493119
  have htrace : WordTrace (prefixWord ++ tailWord_6493119) baseStart_6493119 baseEnd_6493119 := by
    simpa [prefixWord, tailWord_6493119, baseEnd_6493119] using wordTrace_append hprefix tailTrace_6493119
  have hstable : (prefixWord ++ tailWord_6493119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493119).length < 2 ^ (prefixWord ++ tailWord_6493119).sum := by decide
  have hdescent : baseEnd_6493119 < baseStart_6493119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493120 : List Nat := [2, 1, 1, 2, 3, 5, 1, 2, 1, 3, 2]
def baseStart_6493120 : Nat := 118140960795 + 6493120 * 2 ^ 59
def prefixEnd_6493120 : Nat := 4983230072969 + 3 ^ 40 * 6493120 * 2
def baseEnd_6493120 : Nat := 3334091507321740871838691

theorem tailTrace_6493120 : CollatzResearch.WordTrace tailWord_6493120 prefixEnd_6493120 3334091507321740871838691 := by
  unfold tailWord_6493120
  simp only [CollatzResearch.WordTrace]
  refine ⟨118411771118271325727078407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157882361491028434302771209 118411771118271325727078407)
  ·
    refine ⟨177617656677406988590617611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118411771118271325727078407 177617656677406988590617611)
    ·
      refine ⟨266426485016110482885926417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177617656677406988590617611 266426485016110482885926417)
      ·
        refine ⟨199819863762082862164444813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266426485016110482885926417 199819863762082862164444813)
        ·
          refine ⟨74932448910781073311666805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199819863762082862164444813 74932448910781073311666805)
          ·
            refine ⟨7024917085385725622968763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74932448910781073311666805 7024917085385725622968763)
            ·
              refine ⟨10537375628078588434453145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7024917085385725622968763 10537375628078588434453145)
              ·
                refine ⟨7903031721058941325839859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10537375628078588434453145 7903031721058941325839859)
                ·
                  refine ⟨11854547581588411988759789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7903031721058941325839859 11854547581588411988759789)
                  ·
                    refine ⟨4445455343095654495784921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11854547581588411988759789 4445455343095654495784921)
                    ·
                      refine ⟨3334091507321740871838691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4445455343095654495784921 3334091507321740871838691)
                      ·
                        rfl

theorem cell23_6493120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 1, 3, 2].length) (baseStart_6493120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493120 prefixEnd_6493120 := by exact prefixLift 6493120
  have htrace : WordTrace (prefixWord ++ tailWord_6493120) baseStart_6493120 baseEnd_6493120 := by
    simpa [prefixWord, tailWord_6493120, baseEnd_6493120] using wordTrace_append hprefix tailTrace_6493120
  have hstable : (prefixWord ++ tailWord_6493120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493120).length < 2 ^ (prefixWord ++ tailWord_6493120).sum := by decide
  have hdescent : baseEnd_6493120 < baseStart_6493120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493176 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 4, 5, 2]
def baseStart_6493176 : Nat := 118140960795 + 6493176 * 2 ^ 59
def prefixEnd_6493176 : Nat := 4983230072969 + 3 ^ 40 * 6493176 * 2
def baseEnd_6493176 : Nat := 3334120262238392652738433

theorem tailTrace_6493176 : CollatzResearch.WordTrace tailWord_6493176 prefixEnd_6493176 3334120262238392652738433 := by
  unfold tailWord_6493176
  simp only [CollatzResearch.WordTrace]
  refine ⟨118412792362169886509097691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157883723149559848678796921 118412792362169886509097691)
  ·
    refine ⟨177619188543254829763646537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118412792362169886509097691 177619188543254829763646537)
    ·
      refine ⟨133214391407441122322734903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177619188543254829763646537 133214391407441122322734903)
      ·
        refine ⟨199821587111161683484102355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133214391407441122322734903 199821587111161683484102355)
        ·
          refine ⟨299732380666742525226153533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199821587111161683484102355 299732380666742525226153533)
          ·
            refine ⟨112399642750028446959807575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 299732380666742525226153533 112399642750028446959807575)
            ·
              refine ⟨168599464125042670439711363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112399642750028446959807575 168599464125042670439711363)
              ·
                refine ⟨252899196187564005659567045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168599464125042670439711363 252899196187564005659567045)
                ·
                  refine ⟨47418599285168251061168821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252899196187564005659567045 47418599285168251061168821)
                  ·
                    refine ⟨4445493682984523536984577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47418599285168251061168821 4445493682984523536984577)
                    ·
                      refine ⟨3334120262238392652738433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4445493682984523536984577 3334120262238392652738433)
                      ·
                        rfl

theorem cell23_6493176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4, 5, 2].length) (baseStart_6493176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493176 prefixEnd_6493176 := by exact prefixLift 6493176
  have htrace : WordTrace (prefixWord ++ tailWord_6493176) baseStart_6493176 baseEnd_6493176 := by
    simpa [prefixWord, tailWord_6493176, baseEnd_6493176] using wordTrace_append hprefix tailTrace_6493176
  have hstable : (prefixWord ++ tailWord_6493176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493176).length < 2 ^ (prefixWord ++ tailWord_6493176).sum := by decide
  have hdescent : baseEnd_6493176 < baseStart_6493176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493209 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 2, 3, 5]
def baseStart_6493209 : Nat := 118140960795 + 6493209 * 2 ^ 59
def prefixEnd_6493209 : Nat := 4983230072969 + 3 ^ 40 * 6493209 * 2
def baseEnd_6493209 : Nat := 3334137207099991023625781

theorem tailTrace_6493209 : CollatzResearch.WordTrace tailWord_6493209 prefixEnd_6493209 3334137207099991023625781 := by
  unfold tailWord_6493209
  simp only [CollatzResearch.WordTrace]
  refine ⟨236826788333220219654146681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157884525555480146436097787 236826788333220219654146681)
  ·
    refine ⟨177620091249915164740610011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236826788333220219654146681 177620091249915164740610011)
    ·
      refine ⟨266430136874872747110915017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177620091249915164740610011 266430136874872747110915017)
      ·
        refine ⟨199822602656154560333186263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266430136874872747110915017 199822602656154560333186263)
        ·
          refine ⟨299733903984231840499779395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199822602656154560333186263 299733903984231840499779395)
          ·
            refine ⟨449600855976347760749669093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299733903984231840499779395 449600855976347760749669093)
            ·
              refine ⟨84300160495565205140562955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 449600855976347760749669093 84300160495565205140562955)
              ·
                refine ⟨126450240743347807710844433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84300160495565205140562955 126450240743347807710844433)
                ·
                  refine ⟨94837680557510855783133325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126450240743347807710844433 94837680557510855783133325)
                  ·
                    refine ⟨35564130209066570918674997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 94837680557510855783133325 35564130209066570918674997)
                    ·
                      refine ⟨3334137207099991023625781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35564130209066570918674997 3334137207099991023625781)
                      ·
                        rfl

theorem cell23_6493209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_6493209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493209 prefixEnd_6493209 := by exact prefixLift 6493209
  have htrace : WordTrace (prefixWord ++ tailWord_6493209) baseStart_6493209 baseEnd_6493209 := by
    simpa [prefixWord, tailWord_6493209, baseEnd_6493209] using wordTrace_append hprefix tailTrace_6493209
  have hstable : (prefixWord ++ tailWord_6493209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493209).length < 2 ^ (prefixWord ++ tailWord_6493209).sum := by decide
  have hdescent : baseEnd_6493209 < baseStart_6493209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493223 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_6493223 : Nat := 118140960795 + 6493223 * 2 ^ 59
def prefixEnd_6493223 : Nat := 4983230072969 + 3 ^ 40 * 6493223 * 2
def baseEnd_6493223 : Nat := 3334144395829153968850717

theorem tailTrace_6493223 : CollatzResearch.WordTrace tailWord_6493223 prefixEnd_6493223 3334144395829153968850717 := by
  unfold tailWord_6493223
  simp only [CollatzResearch.WordTrace]
  refine ⟨236827298955169500045156323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157884865970113000030104215 236827298955169500045156323)
  ·
    refine ⟨355240948432754250067734485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236827298955169500045156323 355240948432754250067734485)
    ·
      refine ⟨8325959728892677735962527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 355240948432754250067734485 8325959728892677735962527)
      ·
        refine ⟨12488939593339016603943791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8325959728892677735962527 12488939593339016603943791)
        ·
          refine ⟨18733409390008524905915687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12488939593339016603943791 18733409390008524905915687)
          ·
            refine ⟨28100114085012787358873531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18733409390008524905915687 28100114085012787358873531)
            ·
              refine ⟨42150171127519181038310297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28100114085012787358873531 42150171127519181038310297)
              ·
                refine ⟨31612628345639385778732723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42150171127519181038310297 31612628345639385778732723)
                ·
                  refine ⟨47418942518459078668099085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31612628345639385778732723 47418942518459078668099085)
                  ·
                    refine ⟨17782103444422154500537157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47418942518459078668099085 17782103444422154500537157)
                    ·
                      refine ⟨3334144395829153968850717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17782103444422154500537157 3334144395829153968850717)
                      ·
                        rfl

theorem cell23_6493223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_6493223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493223 prefixEnd_6493223 := by exact prefixLift 6493223
  have htrace : WordTrace (prefixWord ++ tailWord_6493223) baseStart_6493223 baseEnd_6493223 := by
    simpa [prefixWord, tailWord_6493223, baseEnd_6493223] using wordTrace_append hprefix tailTrace_6493223
  have hstable : (prefixWord ++ tailWord_6493223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493223).length < 2 ^ (prefixWord ++ tailWord_6493223).sum := by decide
  have hdescent : baseEnd_6493223 < baseStart_6493223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493273 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 3, 1, 3]
def baseStart_6493273 : Nat := 118140960795 + 6493273 * 2 ^ 59
def prefixEnd_6493273 : Nat := 4983230072969 + 3 ^ 40 * 6493273 * 2
def baseEnd_6493273 : Nat := 3334170069861878773225487

theorem tailTrace_6493273 : CollatzResearch.WordTrace tailWord_6493273 prefixEnd_6493273 3334170069861878773225487 := by
  unfold tailWord_6493273
  simp only [CollatzResearch.WordTrace]
  refine ⟨236829122604988358584476473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157886081736658905722984315 236829122604988358584476473)
  ·
    refine ⟨177621841953741268938357355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236829122604988358584476473 177621841953741268938357355)
    ·
      refine ⟨266432762930611903407536033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177621841953741268938357355 266432762930611903407536033)
      ·
        refine ⟨199824572197958927555652025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266432762930611903407536033 199824572197958927555652025)
        ·
          refine ⟨149868429148469195666739019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199824572197958927555652025 149868429148469195666739019)
          ·
            refine ⟨224802643722703793500108529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149868429148469195666739019 224802643722703793500108529)
            ·
              refine ⟨168601982792027845125081397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224802643722703793500108529 168601982792027845125081397)
              ·
                refine ⟨15806435886752610480476381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 168601982792027845125081397 15806435886752610480476381)
                ·
                  refine ⟨5927413457532228930178643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15806435886752610480476381 5927413457532228930178643)
                  ·
                    refine ⟨8891120186298343395267965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5927413457532228930178643 8891120186298343395267965)
                    ·
                      refine ⟨3334170069861878773225487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8891120186298343395267965 3334170069861878773225487)
                      ·
                        rfl

theorem cell23_6493273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 1, 3].length) (baseStart_6493273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493273 prefixEnd_6493273 := by exact prefixLift 6493273
  have htrace : WordTrace (prefixWord ++ tailWord_6493273) baseStart_6493273 baseEnd_6493273 := by
    simpa [prefixWord, tailWord_6493273, baseEnd_6493273] using wordTrace_append hprefix tailTrace_6493273
  have hstable : (prefixWord ++ tailWord_6493273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493273).length < 2 ^ (prefixWord ++ tailWord_6493273).sum := by decide
  have hdescent : baseEnd_6493273 < baseStart_6493273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493283 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 6, 3, 2]
def baseStart_6493283 : Nat := 118140960795 + 6493283 * 2 ^ 59
def prefixEnd_6493283 : Nat := 4983230072969 + 3 ^ 40 * 6493283 * 2
def baseEnd_6493283 : Nat := 3334175204668423734100441

theorem tailTrace_6493283 : CollatzResearch.WordTrace tailWord_6493283 prefixEnd_6493283 3334175204668423734100441 := by
  unfold tailWord_6493283
  simp only [CollatzResearch.WordTrace]
  refine ⟨236829487334952130292340503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157886324889968086861560335 236829487334952130292340503)
  ·
    refine ⟨355244231002428195438510755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236829487334952130292340503 355244231002428195438510755)
    ·
      refine ⟨532866346503642293157766133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355244231002428195438510755 532866346503642293157766133)
      ·
        refine ⟨49956219984716464983540575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 532866346503642293157766133 49956219984716464983540575)
        ·
          refine ⟨74934329977074697475310863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49956219984716464983540575 74934329977074697475310863)
          ·
            refine ⟨112401494965612046212966295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74934329977074697475310863 112401494965612046212966295)
            ·
              refine ⟨168602242448418069319449443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112401494965612046212966295 168602242448418069319449443)
              ·
                refine ⟨252903363672627103979174165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168602242448418069319449443 252903363672627103979174165)
                ·
                  refine ⟨11854845172154395499023789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 252903363672627103979174165 11854845172154395499023789)
                  ·
                    refine ⟨4445566939557898312133921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11854845172154395499023789 4445566939557898312133921)
                    ·
                      refine ⟨3334175204668423734100441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4445566939557898312133921 3334175204668423734100441)
                      ·
                        rfl

theorem cell23_6493283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_6493283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493283 prefixEnd_6493283 := by exact prefixLift 6493283
  have htrace : WordTrace (prefixWord ++ tailWord_6493283) baseStart_6493283 baseEnd_6493283 := by
    simpa [prefixWord, tailWord_6493283, baseEnd_6493283] using wordTrace_append hprefix tailTrace_6493283
  have hstable : (prefixWord ++ tailWord_6493283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493283).length < 2 ^ (prefixWord ++ tailWord_6493283).sum := by decide
  have hdescent : baseEnd_6493283 < baseStart_6493283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493293 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 3, 5]
def baseStart_6493293 : Nat := 118140960795 + 6493293 * 2 ^ 59
def prefixEnd_6493293 : Nat := 4983230072969 + 3 ^ 40 * 6493293 * 2
def baseEnd_6493293 : Nat := 1111393446491656231658465

theorem tailTrace_6493293 : CollatzResearch.WordTrace tailWord_6493293 prefixEnd_6493293 1111393446491656231658465 := by
  unfold tailWord_6493293
  simp only [CollatzResearch.WordTrace]
  refine ⟨236829852064915902000204533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157886568043277268000136355 236829852064915902000204533)
  ·
    refine ⟨22202798631085865812519175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 236829852064915902000204533 22202798631085865812519175)
    ·
      refine ⟨33304197946628798718778763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22202798631085865812519175 33304197946628798718778763)
      ·
        refine ⟨49956296919943198078168145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33304197946628798718778763 49956296919943198078168145)
        ·
          refine ⟨37467222689957398558626109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49956296919943198078168145 37467222689957398558626109)
          ·
            refine ⟨14050208508734024459484791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37467222689957398558626109 14050208508734024459484791)
            ·
              refine ⟨21075312763101036689227187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14050208508734024459484791 21075312763101036689227187)
              ·
                refine ⟨31612969144651555033840781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21075312763101036689227187 31612969144651555033840781)
                ·
                  refine ⟨11854863429244333137690293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31612969144651555033840781 11854863429244333137690293)
                  ·
                    refine ⟨1111393446491656231658465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11854863429244333137690293 1111393446491656231658465)
                    ·
                      rfl

theorem cell23_6493293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 5].length) (baseStart_6493293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493293 prefixEnd_6493293 := by exact prefixLift 6493293
  have htrace : WordTrace (prefixWord ++ tailWord_6493293) baseStart_6493293 baseEnd_6493293 := by
    simpa [prefixWord, tailWord_6493293, baseEnd_6493293] using wordTrace_append hprefix tailTrace_6493293
  have hstable : (prefixWord ++ tailWord_6493293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493293).length < 2 ^ (prefixWord ++ tailWord_6493293).sum := by decide
  have hdescent : baseEnd_6493293 < baseStart_6493293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493340 : List Nat := [2, 2, 3, 2, 1, 2, 2, 3, 2, 4]
def baseStart_6493340 : Nat := 118140960795 + 6493340 * 2 ^ 59
def prefixEnd_6493340 : Nat := 4983230072969 + 3 ^ 40 * 6493340 * 2
def baseEnd_6493340 : Nat := 1111401491021910003695893

theorem tailTrace_6493340 : CollatzResearch.WordTrace tailWord_6493340 prefixEnd_6493340 1111401491021910003695893 := by
  unfold tailWord_6493340
  simp only [CollatzResearch.WordTrace]
  refine ⟨118415783147872814513582737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157887710863830419351443649 118415783147872814513582737)
  ·
    refine ⟨88811837360904610885187053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118415783147872814513582737 88811837360904610885187053)
    ·
      refine ⟨33304439010339229081945145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88811837360904610885187053 33304439010339229081945145)
      ·
        refine ⟨24978329257754421811458859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33304439010339229081945145 24978329257754421811458859)
        ·
          refine ⟨37467493886631632717188289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24978329257754421811458859 37467493886631632717188289)
          ·
            refine ⟨28100620414973724537891217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37467493886631632717188289 28100620414973724537891217)
            ·
              refine ⟨21075465311230293403418413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28100620414973724537891217 21075465311230293403418413)
              ·
                refine ⟨7903299491711360026281905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21075465311230293403418413 7903299491711360026281905)
                ·
                  refine ⟨5927474618783520019711429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7903299491711360026281905 5927474618783520019711429)
                  ·
                    refine ⟨1111401491021910003695893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5927474618783520019711429 1111401491021910003695893)
                    ·
                      rfl

theorem cell23_6493340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_6493340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493340 prefixEnd_6493340 := by exact prefixLift 6493340
  have htrace : WordTrace (prefixWord ++ tailWord_6493340) baseStart_6493340 baseEnd_6493340 := by
    simpa [prefixWord, tailWord_6493340, baseEnd_6493340] using wordTrace_append hprefix tailTrace_6493340
  have hstable : (prefixWord ++ tailWord_6493340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493340).length < 2 ^ (prefixWord ++ tailWord_6493340).sum := by decide
  have hdescent : baseEnd_6493340 < baseStart_6493340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493363 : List Nat := [1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 3]
def baseStart_6493363 : Nat := 118140960795 + 6493363 * 2 ^ 59
def prefixEnd_6493363 : Nat := 4983230072969 + 3 ^ 40 * 6493363 * 2
def baseEnd_6493363 : Nat := 3334216283120783421100073

theorem tailTrace_6493363 : CollatzResearch.WordTrace tailWord_6493363 prefixEnd_6493363 3334216283120783421100073 := by
  unfold tailWord_6493363
  simp only [CollatzResearch.WordTrace]
  refine ⟨236832405174662303955252743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157888270116441535970168495 236832405174662303955252743)
  ·
    refine ⟨355248607761993455932879115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236832405174662303955252743 355248607761993455932879115)
    ·
      refine ⟨532872911642990183899318673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355248607761993455932879115 532872911642990183899318673)
      ·
        refine ⟨399654683732242637924489005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532872911642990183899318673 399654683732242637924489005)
        ·
          refine ⟨149870506399590989221683377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399654683732242637924489005 149870506399590989221683377)
          ·
            refine ⟨112402879799693241916262533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149870506399590989221683377 112402879799693241916262533)
            ·
              refine ⟨21075539962442482859299225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112402879799693241916262533 21075539962442482859299225)
              ·
                refine ⟨15806654971831862144474419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21075539962442482859299225 15806654971831862144474419)
                ·
                  refine ⟨23709982457747793216711629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15806654971831862144474419 23709982457747793216711629)
                  ·
                    refine ⟨8891243421655422456266861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23709982457747793216711629 8891243421655422456266861)
                    ·
                      refine ⟨3334216283120783421100073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8891243421655422456266861 3334216283120783421100073)
                      ·
                        rfl

theorem cell23_6493363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 3].length) (baseStart_6493363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493363 prefixEnd_6493363 := by exact prefixLift 6493363
  have htrace : WordTrace (prefixWord ++ tailWord_6493363) baseStart_6493363 baseEnd_6493363 := by
    simpa [prefixWord, tailWord_6493363, baseEnd_6493363] using wordTrace_append hprefix tailTrace_6493363
  have hstable : (prefixWord ++ tailWord_6493363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493363).length < 2 ^ (prefixWord ++ tailWord_6493363).sum := by decide
  have hdescent : baseEnd_6493363 < baseStart_6493363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493397 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 1, 3, 3]
def baseStart_6493397 : Nat := 118140960795 + 6493397 * 2 ^ 59
def prefixEnd_6493397 : Nat := 4983230072969 + 3 ^ 40 * 6493397 * 2
def baseEnd_6493397 : Nat := 3334233741463036288074917

theorem tailTrace_6493397 : CollatzResearch.WordTrace tailWord_6493397 prefixEnd_6493397 3334233741463036288074917 := by
  unfold tailWord_6493397
  simp only [CollatzResearch.WordTrace]
  refine ⟨236833645256539127761990445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157889096837692751841326963 236833645256539127761990445)
  ·
    refine ⟨88812616971202172910746417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236833645256539127761990445 88812616971202172910746417)
    ·
      refine ⟨66609462728401629683059813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88812616971202172910746417 66609462728401629683059813)
      ·
        refine ⟨12489274261575305565573715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66609462728401629683059813 12489274261575305565573715)
        ·
          refine ⟨18733911392362958348360573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12489274261575305565573715 18733911392362958348360573)
          ·
            refine ⟨7025216772136109380635215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18733911392362958348360573 7025216772136109380635215)
            ·
              refine ⟨10537825158204164070952823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7025216772136109380635215 10537825158204164070952823)
              ·
                refine ⟨15806737737306246106429235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10537825158204164070952823 15806737737306246106429235)
                ·
                  refine ⟨23710106605959369159643853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15806737737306246106429235 23710106605959369159643853)
                  ·
                    refine ⟨8891289977234763434866445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23710106605959369159643853 8891289977234763434866445)
                    ·
                      refine ⟨3334233741463036288074917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8891289977234763434866445 3334233741463036288074917)
                      ·
                        rfl

theorem cell23_6493397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_6493397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493397 prefixEnd_6493397 := by exact prefixLift 6493397
  have htrace : WordTrace (prefixWord ++ tailWord_6493397) baseStart_6493397 baseEnd_6493397 := by
    simpa [prefixWord, tailWord_6493397, baseEnd_6493397] using wordTrace_append hprefix tailTrace_6493397
  have hstable : (prefixWord ++ tailWord_6493397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493397).length < 2 ^ (prefixWord ++ tailWord_6493397).sum := by decide
  have hdescent : baseEnd_6493397 < baseStart_6493397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493443 : List Nat := [1, 1, 1, 3, 2, 4, 3, 1, 7]
def baseStart_6493443 : Nat := 118140960795 + 6493443 * 2 ^ 59
def prefixEnd_6493443 : Nat := 4983230072969 + 3 ^ 40 * 6493443 * 2
def baseEnd_6493443 : Nat := 370473040174793678677745

theorem tailTrace_6493443 : CollatzResearch.WordTrace tailWord_6493443 prefixEnd_6493443 370473040174793678677745 := by
  unfold tailWord_6493443
  simp only [CollatzResearch.WordTrace]
  refine ⟨236835323014372477618164983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157890215342914985078776655 236835323014372477618164983)
  ·
    refine ⟨355252984521558716427247475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236835323014372477618164983 355252984521558716427247475)
    ·
      refine ⟨532879476782338074640871213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355252984521558716427247475 532879476782338074640871213)
      ·
        refine ⟨199829803793376777990326705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 532879476782338074640871213 199829803793376777990326705)
        ·
          refine ⟨149872352845032583492745029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199829803793376777990326705 149872352845032583492745029)
          ·
            refine ⟨28101066158443609404889693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149872352845032583492745029 28101066158443609404889693)
            ·
              refine ⟨10537899809416353526833635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28101066158443609404889693 10537899809416353526833635)
              ·
                refine ⟨15806849714124530290250453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10537899809416353526833635 15806849714124530290250453)
                ·
                  refine ⟨370473040174793678677745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15806849714124530290250453 370473040174793678677745)
                  ·
                    rfl

theorem cell23_6493443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 3, 1, 7].length) (baseStart_6493443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493443 prefixEnd_6493443 := by exact prefixLift 6493443
  have htrace : WordTrace (prefixWord ++ tailWord_6493443) baseStart_6493443 baseEnd_6493443 := by
    simpa [prefixWord, tailWord_6493443, baseEnd_6493443] using wordTrace_append hprefix tailTrace_6493443
  have hstable : (prefixWord ++ tailWord_6493443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493443).length < 2 ^ (prefixWord ++ tailWord_6493443).sum := by decide
  have hdescent : baseEnd_6493443 < baseStart_6493443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493454 : List Nat := [4, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2]
def baseStart_6493454 : Nat := 118140960795 + 6493454 * 2 ^ 59
def prefixEnd_6493454 : Nat := 4983230072969 + 3 ^ 40 * 6493454 * 2
def baseEnd_6493454 : Nat := 3334263009860342565062155

theorem tailTrace_6493454 : CollatzResearch.WordTrace tailWord_6493454 prefixEnd_6493454 3334263009860342565062155 := by
  unfold tailWord_6493454
  simp only [CollatzResearch.WordTrace]
  refine ⟨29604465527166578312101927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157890482811555084331210277 29604465527166578312101927)
  ·
    refine ⟨44406698290749867468152891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29604465527166578312101927 44406698290749867468152891)
    ·
      refine ⟨66610047436124801202229337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44406698290749867468152891 66610047436124801202229337)
      ·
        refine ⟨49957535577093600901672003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66610047436124801202229337 49957535577093600901672003)
        ·
          refine ⟨74936303365640401352508005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49957535577093600901672003 74936303365640401352508005)
          ·
            refine ⟨14050556881057575253595251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74936303365640401352508005 14050556881057575253595251)
            ·
              refine ⟨21075835321586362880392877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14050556881057575253595251 21075835321586362880392877)
              ·
                refine ⟨7903438245594886080147329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21075835321586362880392877 7903438245594886080147329)
                ·
                  refine ⟨5927578684196164560110497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7903438245594886080147329 5927578684196164560110497)
                  ·
                    refine ⟨4445684013147123420082873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5927578684196164560110497 4445684013147123420082873)
                    ·
                      refine ⟨3334263009860342565062155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4445684013147123420082873 3334263009860342565062155)
                      ·
                        rfl

theorem cell23_6493454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_6493454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493454 prefixEnd_6493454 := by exact prefixLift 6493454
  have htrace : WordTrace (prefixWord ++ tailWord_6493454) baseStart_6493454 baseEnd_6493454 := by
    simpa [prefixWord, tailWord_6493454, baseEnd_6493454] using wordTrace_append hprefix tailTrace_6493454
  have hstable : (prefixWord ++ tailWord_6493454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493454).length < 2 ^ (prefixWord ++ tailWord_6493454).sum := by decide
  have hdescent : baseEnd_6493454 < baseStart_6493454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493458 : List Nat := [3, 2, 4, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_6493458 : Nat := 118140960795 + 6493458 * 2 ^ 59
def prefixEnd_6493458 : Nat := 4983230072969 + 3 ^ 40 * 6493458 * 2
def baseEnd_6493458 : Nat := 3334265063782960549412137

theorem tailTrace_6493458 : CollatzResearch.WordTrace tailWord_6493458 prefixEnd_6493458 3334265063782960549412137 := by
  unfold tailWord_6493458
  simp only [CollatzResearch.WordTrace]
  refine ⟨59208967527329533794990257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157890580072878756786640685 59208967527329533794990257)
  ·
    refine ⟨44406725645497150346242693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59208967527329533794990257 44406725645497150346242693)
    ·
      refine ⟨8326261058530715689920505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44406725645497150346242693 8326261058530715689920505)
      ·
        refine ⟨6244695793898036767440379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8326261058530715689920505 6244695793898036767440379)
        ·
          refine ⟨9367043690847055151160569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6244695793898036767440379 9367043690847055151160569)
          ·
            refine ⟨7025282768135291363370427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9367043690847055151160569 7025282768135291363370427)
            ·
              refine ⟨10537924152202937045055641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7025282768135291363370427 10537924152202937045055641)
              ·
                refine ⟨7903443114152202783791731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10537924152202937045055641 7903443114152202783791731)
                ·
                  refine ⟨11855164671228304175687597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7903443114152202783791731 11855164671228304175687597)
                  ·
                    refine ⟨4445686751710614065882849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11855164671228304175687597 4445686751710614065882849)
                    ·
                      refine ⟨3334265063782960549412137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4445686751710614065882849 3334265063782960549412137)
                      ·
                        rfl

theorem cell23_6493458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_6493458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493458 prefixEnd_6493458 := by exact prefixLift 6493458
  have htrace : WordTrace (prefixWord ++ tailWord_6493458) baseStart_6493458 baseEnd_6493458 := by
    simpa [prefixWord, tailWord_6493458, baseEnd_6493458] using wordTrace_append hprefix tailTrace_6493458
  have hstable : (prefixWord ++ tailWord_6493458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493458).length < 2 ^ (prefixWord ++ tailWord_6493458).sum := by decide
  have hdescent : baseEnd_6493458 < baseStart_6493458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493490 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 2, 5]
def baseStart_6493490 : Nat := 118140960795 + 6493490 * 2 ^ 59
def prefixEnd_6493490 : Nat := 4983230072969 + 3 ^ 40 * 6493490 * 2
def baseEnd_6493490 : Nat := 1111427165054634808070663

theorem tailTrace_6493490 : CollatzResearch.WordTrace tailWord_6493490 prefixEnd_6493490 1111427165054634808070663 := by
  unfold tailWord_6493490
  simp only [CollatzResearch.WordTrace]
  refine ⟨59209259311300551161281481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157891358163468136430083949 59209259311300551161281481)
  ·
    refine ⟨44406944483475413370961111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59209259311300551161281481 44406944483475413370961111)
    ·
      refine ⟨66610416725213120056441667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44406944483475413370961111 66610416725213120056441667)
      ·
        refine ⟨99915625087819680084662501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66610416725213120056441667 99915625087819680084662501)
        ·
          refine ⟨18734179703966190015874219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 99915625087819680084662501 18734179703966190015874219)
          ·
            refine ⟨28101269555949285023811329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18734179703966190015874219 28101269555949285023811329)
            ·
              refine ⟨21075952166961963767858497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28101269555949285023811329 21075952166961963767858497)
              ·
                refine ⟨15806964125221472825893873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21075952166961963767858497 15806964125221472825893873)
                ·
                  refine ⟨11855223093916104619420405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15806964125221472825893873 11855223093916104619420405)
                  ·
                    refine ⟨1111427165054634808070663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11855223093916104619420405 1111427165054634808070663)
                    ·
                      rfl

theorem cell23_6493490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_6493490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493490 prefixEnd_6493490 := by exact prefixLift 6493490
  have htrace : WordTrace (prefixWord ++ tailWord_6493490) baseStart_6493490 baseEnd_6493490 := by
    simpa [prefixWord, tailWord_6493490, baseEnd_6493490] using wordTrace_append hprefix tailTrace_6493490
  have hstable : (prefixWord ++ tailWord_6493490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493490).length < 2 ^ (prefixWord ++ tailWord_6493490).sum := by decide
  have hdescent : baseEnd_6493490 < baseStart_6493490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493520 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 3, 4]
def baseStart_6493520 : Nat := 118140960795 + 6493520 * 2 ^ 59
def prefixEnd_6493520 : Nat := 4983230072969 + 3 ^ 40 * 6493520 * 2
def baseEnd_6493520 : Nat := 1111432299861179768945617

theorem tailTrace_6493520 : CollatzResearch.WordTrace tailWord_6493520 prefixEnd_6493520 1111432299861179768945617 := by
  unfold tailWord_6493520
  simp only [CollatzResearch.WordTrace]
  refine ⟨118419065717546759884359007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157892087623395679845812009 118419065717546759884359007)
  ·
    refine ⟨177628598576320139826538511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118419065717546759884359007 177628598576320139826538511)
    ·
      refine ⟨266442897864480209739807767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177628598576320139826538511 266442897864480209739807767)
      ·
        refine ⟨399664346796720314609711651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266442897864480209739807767 399664346796720314609711651)
        ·
          refine ⟨599496520195080471914567477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399664346796720314609711651 599496520195080471914567477)
          ·
            refine ⟨56202798768288794241990701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 599496520195080471914567477 56202798768288794241990701)
            ·
              refine ⟨21076049538108297840746513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56202798768288794241990701 21076049538108297840746513)
              ·
                refine ⟨15807037153581223380559885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21076049538108297840746513 15807037153581223380559885)
                ·
                  refine ⟨5927638932592958767709957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15807037153581223380559885 5927638932592958767709957)
                  ·
                    refine ⟨1111432299861179768945617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5927638932592958767709957 1111432299861179768945617)
                    ·
                      rfl

theorem cell23_6493520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 3, 4].length) (baseStart_6493520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493520 prefixEnd_6493520 := by exact prefixLift 6493520
  have htrace : WordTrace (prefixWord ++ tailWord_6493520) baseStart_6493520 baseEnd_6493520 := by
    simpa [prefixWord, tailWord_6493520, baseEnd_6493520] using wordTrace_append hprefix tailTrace_6493520
  have hstable : (prefixWord ++ tailWord_6493520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493520).length < 2 ^ (prefixWord ++ tailWord_6493520).sum := by decide
  have hdescent : baseEnd_6493520 < baseStart_6493520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493527 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 2, 1, 4]
def baseStart_6493527 : Nat := 118140960795 + 6493527 * 2 ^ 59
def prefixEnd_6493527 : Nat := 4983230072969 + 3 ^ 40 * 6493527 * 2
def baseEnd_6493527 : Nat := 3334300493948120779449319

theorem tailTrace_6493527 : CollatzResearch.WordTrace tailWord_6493527 prefixEnd_6493527 3334300493948120779449319 := by
  unfold tailWord_6493527
  simp only [CollatzResearch.WordTrace]
  refine ⟨236838386746068159964222835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157892257830712106642815223 236838386746068159964222835)
  ·
    refine ⟨355257580119102239946334253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236838386746068159964222835 355257580119102239946334253)
    ·
      refine ⟨133221592544663339979875345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355257580119102239946334253 133221592544663339979875345)
      ·
        refine ⟨99916194408497504984906509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133221592544663339979875345 99916194408497504984906509)
        ·
          refine ⟨37468572903186564369339941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 99916194408497504984906509 37468572903186564369339941)
          ·
            refine ⟨7025357419347480819251239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37468572903186564369339941 7025357419347480819251239)
            ·
              refine ⟨10538036129021221228876859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7025357419347480819251239 10538036129021221228876859)
              ·
                refine ⟨15807054193531831843315289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10538036129021221228876859 15807054193531831843315289)
                ·
                  refine ⟨11855290645148873882486467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15807054193531831843315289 11855290645148873882486467)
                  ·
                    refine ⟨17782935967723310823729701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11855290645148873882486467 17782935967723310823729701)
                    ·
                      refine ⟨3334300493948120779449319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17782935967723310823729701 3334300493948120779449319)
                      ·
                        rfl

theorem cell23_6493527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_6493527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493527 prefixEnd_6493527 := by exact prefixLift 6493527
  have htrace : WordTrace (prefixWord ++ tailWord_6493527) baseStart_6493527 baseEnd_6493527 := by
    simpa [prefixWord, tailWord_6493527, baseEnd_6493527] using wordTrace_append hprefix tailTrace_6493527
  have hstable : (prefixWord ++ tailWord_6493527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493527).length < 2 ^ (prefixWord ++ tailWord_6493527).sum := by decide
  have hdescent : baseEnd_6493527 < baseStart_6493527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493553 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 1, 2, 6]
def baseStart_6493553 : Nat := 118140960795 + 6493553 * 2 ^ 59
def prefixEnd_6493553 : Nat := 4983230072969 + 3 ^ 40 * 6493553 * 2
def baseEnd_6493553 : Nat := 3334313844445137677724199

theorem tailTrace_6493553 : CollatzResearch.WordTrace tailWord_6493553 prefixEnd_6493553 3334313844445137677724199 := by
  unfold tailWord_6493553
  simp only [CollatzResearch.WordTrace]
  refine ⟨236839335043973966404669313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157892890029315977603112875 236839335043973966404669313)
  ·
    refine ⟨177629501282980474803501985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236839335043973966404669313 177629501282980474803501985)
    ·
      refine ⟨133222125962235356102626489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177629501282980474803501985 133222125962235356102626489)
      ·
        refine ⟨99916594471676517076969867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133222125962235356102626489 99916594471676517076969867)
        ·
          refine ⟨149874891707514775615454801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99916594471676517076969867 149874891707514775615454801)
          ·
            refine ⟨112406168780636081711591101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149874891707514775615454801 112406168780636081711591101)
            ·
              refine ⟨42152313292738530641846663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112406168780636081711591101 42152313292738530641846663)
              ·
                refine ⟨63228469939107795962769995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42152313292738530641846663 63228469939107795962769995)
                ·
                  refine ⟨94842704908661693944154993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63228469939107795962769995 94842704908661693944154993)
                  ·
                    refine ⟨71132028681496270458116245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94842704908661693944154993 71132028681496270458116245)
                    ·
                      refine ⟨3334313844445137677724199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71132028681496270458116245 3334313844445137677724199)
                      ·
                        rfl

theorem cell23_6493553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_6493553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493553 prefixEnd_6493553 := by exact prefixLift 6493553
  have htrace : WordTrace (prefixWord ++ tailWord_6493553) baseStart_6493553 baseEnd_6493553 := by
    simpa [prefixWord, tailWord_6493553, baseEnd_6493553] using wordTrace_append hprefix tailTrace_6493553
  have hstable : (prefixWord ++ tailWord_6493553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493553).length < 2 ^ (prefixWord ++ tailWord_6493553).sum := by decide
  have hdescent : baseEnd_6493553 < baseStart_6493553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493573 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 7]
def baseStart_6493573 : Nat := 118140960795 + 6493573 * 2 ^ 59
def prefixEnd_6493573 : Nat := 4983230072969 + 3 ^ 40 * 6493573 * 2
def baseEnd_6493573 : Nat := 3334324114058227599474107

theorem tailTrace_6493573 : CollatzResearch.WordTrace tailWord_6493573 prefixEnd_6493573 3334324114058227599474107 := by
  unfold tailWord_6493573
  simp only [CollatzResearch.WordTrace]
  refine ⟨236840064503901509820397373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157893376335934339880264915 236840064503901509820397373)
  ·
    refine ⟨88815024188963066182649015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236840064503901509820397373 88815024188963066182649015)
    ·
      refine ⟨133222536283444599273973523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88815024188963066182649015 133222536283444599273973523)
      ·
        refine ⟨199833804425166898910960285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133222536283444599273973523 199833804425166898910960285)
        ·
          refine ⟨74937676659437587091610107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199833804425166898910960285 74937676659437587091610107)
          ·
            refine ⟨112406514989156380637415161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74937676659437587091610107 112406514989156380637415161)
            ·
              refine ⟨84304886241867285478061371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112406514989156380637415161 84304886241867285478061371)
              ·
                refine ⟨126457329362800928217092057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84304886241867285478061371 126457329362800928217092057)
                ·
                  refine ⟨94842997022100696162819043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126457329362800928217092057 94842997022100696162819043)
                  ·
                    refine ⟨142264495533151044244228565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94842997022100696162819043 142264495533151044244228565)
                    ·
                      refine ⟨3334324114058227599474107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142264495533151044244228565 3334324114058227599474107)
                      ·
                        rfl

theorem cell23_6493573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_6493573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493573 prefixEnd_6493573 := by exact prefixLift 6493573
  have htrace : WordTrace (prefixWord ++ tailWord_6493573) baseStart_6493573 baseEnd_6493573 := by
    simpa [prefixWord, tailWord_6493573, baseEnd_6493573] using wordTrace_append hprefix tailTrace_6493573
  have hstable : (prefixWord ++ tailWord_6493573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493573).length < 2 ^ (prefixWord ++ tailWord_6493573).sum := by decide
  have hdescent : baseEnd_6493573 < baseStart_6493573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493597 : List Nat := [1, 4, 2, 1, 3, 1, 2, 3, 1, 5]
def baseStart_6493597 : Nat := 118140960795 + 6493597 * 2 ^ 59
def prefixEnd_6493597 : Nat := 4983230072969 + 3 ^ 40 * 6493597 * 2
def baseEnd_6493597 : Nat := 1111445479197978501857999

theorem tailTrace_6493597 : CollatzResearch.WordTrace tailWord_6493597 prefixEnd_6493597 1111445479197978501857999 := by
  unfold tailWord_6493597
  simp only [CollatzResearch.WordTrace]
  refine ⟨236840939855814561919271045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157893959903876374612847363 236840939855814561919271045)
  ·
    refine ⟨44407676222965230359863321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236840939855814561919271045 44407676222965230359863321)
    ·
      refine ⟨33305757167223922769897491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44407676222965230359863321 33305757167223922769897491)
      ·
        refine ⟨49958635750835884154846237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33305757167223922769897491 49958635750835884154846237)
        ·
          refine ⟨18734488406563456558067339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49958635750835884154846237 18734488406563456558067339)
          ·
            refine ⟨28101732609845184837101009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18734488406563456558067339 28101732609845184837101009)
            ·
              refine ⟨21076299457383888627825757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28101732609845184837101009 21076299457383888627825757)
              ·
                refine ⟨7903612296518958235434659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21076299457383888627825757 7903612296518958235434659)
                ·
                  refine ⟨11855418444778437353151989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7903612296518958235434659 11855418444778437353151989)
                  ·
                    refine ⟨1111445479197978501857999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11855418444778437353151989 1111445479197978501857999)
                    ·
                      rfl

theorem cell23_6493597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_6493597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493597 prefixEnd_6493597 := by exact prefixLift 6493597
  have htrace : WordTrace (prefixWord ++ tailWord_6493597) baseStart_6493597 baseEnd_6493597 := by
    simpa [prefixWord, tailWord_6493597, baseEnd_6493597] using wordTrace_append hprefix tailTrace_6493597
  have hstable : (prefixWord ++ tailWord_6493597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493597).length < 2 ^ (prefixWord ++ tailWord_6493597).sum := by decide
  have hdescent : baseEnd_6493597 < baseStart_6493597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493654 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_6493654 : Nat := 118140960795 + 6493654 * 2 ^ 59
def prefixEnd_6493654 : Nat := 4983230072969 + 3 ^ 40 * 6493654 * 2
def baseEnd_6493654 : Nat := 3334365705991241782561235

theorem tailTrace_6493654 : CollatzResearch.WordTrace tailWord_6493654 prefixEnd_6493654 3334365705991241782561235 := by
  unfold tailWord_6493654
  simp only [CollatzResearch.WordTrace]
  refine ⟨14802688676038003790881001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157895345877738707102730677 14802688676038003790881001)
  ·
    refine ⟨11102016507028502843160751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14802688676038003790881001 11102016507028502843160751)
    ·
      refine ⟨16653024760542754264741127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11102016507028502843160751 16653024760542754264741127)
      ·
        refine ⟨24979537140814131397111691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16653024760542754264741127 24979537140814131397111691)
        ·
          refine ⟨37469305711221197095667537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24979537140814131397111691 37469305711221197095667537)
          ·
            refine ⟨28101979283415897821750653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37469305711221197095667537 28101979283415897821750653)
            ·
              refine ⟨10538242231280961683156495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28101979283415897821750653 10538242231280961683156495)
              ·
                refine ⟨15807363346921442524734743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10538242231280961683156495 15807363346921442524734743)
                ·
                  refine ⟨23711045020382163787102115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15807363346921442524734743 23711045020382163787102115)
                  ·
                    refine ⟨35566567530573245680653173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23711045020382163787102115 35566567530573245680653173)
                    ·
                      refine ⟨3334365705991241782561235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35566567530573245680653173 3334365705991241782561235)
                      ·
                        rfl

theorem cell23_6493654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_6493654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493654 prefixEnd_6493654 := by exact prefixLift 6493654
  have htrace : WordTrace (prefixWord ++ tailWord_6493654) baseStart_6493654 baseEnd_6493654 := by
    simpa [prefixWord, tailWord_6493654, baseEnd_6493654] using wordTrace_append hprefix tailTrace_6493654
  have hstable : (prefixWord ++ tailWord_6493654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493654).length < 2 ^ (prefixWord ++ tailWord_6493654).sum := by decide
  have hdescent : baseEnd_6493654 < baseStart_6493654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493674 : List Nat := [3, 1, 3, 1, 5, 1, 1, 8]
def baseStart_6493674 : Nat := 118140960795 + 6493674 * 2 ^ 59
def prefixEnd_6493674 : Nat := 4983230072969 + 3 ^ 40 * 6493674 * 2
def baseEnd_6493674 : Nat := 123495406503864137196709

theorem tailTrace_6493674 : CollatzResearch.WordTrace tailWord_6493674 prefixEnd_6493674 123495406503864137196709 := by
  unfold tailWord_6493674
  simp only [CollatzResearch.WordTrace]
  refine ⟨59210937069133901017456019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157895832184357069379882717 59210937069133901017456019)
  ·
    refine ⟨88816405603700851526184029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59210937069133901017456019 88816405603700851526184029)
    ·
      refine ⟨33306152101387819322319011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88816405603700851526184029 33306152101387819322319011)
      ·
        refine ⟨49959228152081728983478517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33306152101387819322319011 49959228152081728983478517)
        ·
          refine ⟨4683677639257662092201111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49959228152081728983478517 4683677639257662092201111)
          ·
            refine ⟨7025516458886493138301667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4683677639257662092201111 7025516458886493138301667)
            ·
              refine ⟨10538274688329739707452501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7025516458886493138301667 10538274688329739707452501)
              ·
                refine ⟨123495406503864137196709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10538274688329739707452501 123495406503864137196709)
                ·
                  rfl

theorem cell23_6493674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 8].length) (baseStart_6493674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493674 prefixEnd_6493674 := by exact prefixLift 6493674
  have htrace : WordTrace (prefixWord ++ tailWord_6493674) baseStart_6493674 baseEnd_6493674 := by
    simpa [prefixWord, tailWord_6493674, baseEnd_6493674] using wordTrace_append hprefix tailTrace_6493674
  have hstable : (prefixWord ++ tailWord_6493674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493674).length < 2 ^ (prefixWord ++ tailWord_6493674).sum := by decide
  have hdescent : baseEnd_6493674 < baseStart_6493674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493690 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4]
def baseStart_6493690 : Nat := 118140960795 + 6493690 * 2 ^ 59
def prefixEnd_6493690 : Nat := 4983230072969 + 3 ^ 40 * 6493690 * 2
def baseEnd_6493690 : Nat := 3334384191294803641711069

theorem tailTrace_6493690 : CollatzResearch.WordTrace tailWord_6493690 prefixEnd_6493690 3334384191294803641711069 := by
  unfold tailWord_6493690
  simp only [CollatzResearch.WordTrace]
  refine ⟨59211082961119409700601631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157896221229651759201604349 59211082961119409700601631)
  ·
    refine ⟨88816624441679114550902447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59211082961119409700601631 88816624441679114550902447)
    ·
      refine ⟨133224936662518671826353671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88816624441679114550902447 133224936662518671826353671)
      ·
        refine ⟨199837404993778007739530507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133224936662518671826353671 199837404993778007739530507)
        ·
          refine ⟨299756107490667011609295761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199837404993778007739530507 299756107490667011609295761)
          ·
            refine ⟨224817080618000258706971821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299756107490667011609295761 224817080618000258706971821)
            ·
              refine ⟨84306405231750097015114433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224817080618000258706971821 84306405231750097015114433)
              ·
                refine ⟨63229803923812572761335825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84306405231750097015114433 63229803923812572761335825)
                ·
                  refine ⟨47422352942859429571001869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63229803923812572761335825 47422352942859429571001869)
                  ·
                    refine ⟨17783382353572286089125701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47422352942859429571001869 17783382353572286089125701)
                    ·
                      refine ⟨3334384191294803641711069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17783382353572286089125701 3334384191294803641711069)
                      ·
                        rfl

theorem cell23_6493690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_6493690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493690 prefixEnd_6493690 := by exact prefixLift 6493690
  have htrace : WordTrace (prefixWord ++ tailWord_6493690) baseStart_6493690 baseEnd_6493690 := by
    simpa [prefixWord, tailWord_6493690, baseEnd_6493690] using wordTrace_append hprefix tailTrace_6493690
  have hstable : (prefixWord ++ tailWord_6493690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493690).length < 2 ^ (prefixWord ++ tailWord_6493690).sum := by decide
  have hdescent : baseEnd_6493690 < baseStart_6493690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493702 : List Nat := [6, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_6493702 : Nat := 118140960795 + 6493702 * 2 ^ 59
def prefixEnd_6493702 : Nat := 4983230072969 + 3 ^ 40 * 6493702 * 2
def baseEnd_6493702 : Nat := 3334390353062657594761015

theorem tailTrace_6493702 : CollatzResearch.WordTrace tailWord_6493702 prefixEnd_6493702 3334390353062657594761015 := by
  unfold tailWord_6493702
  simp only [CollatzResearch.WordTrace]
  refine ⟨7401399047513567651620105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 157896513013622776567895573 7401399047513567651620105)
  ·
    refine ⟨5551049285635175738715079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7401399047513567651620105 5551049285635175738715079)
    ·
      refine ⟨8326573928452763608072619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5551049285635175738715079 8326573928452763608072619)
      ·
        refine ⟨12489860892679145412108929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8326573928452763608072619 12489860892679145412108929)
        ·
          refine ⟨9367395669509359059081697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12489860892679145412108929 9367395669509359059081697)
          ·
            refine ⟨7025546752132019294311273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9367395669509359059081697 7025546752132019294311273)
            ·
              refine ⟨5269160064099014470733455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7025546752132019294311273 5269160064099014470733455)
              ·
                refine ⟨7903740096148521706100183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5269160064099014470733455 7903740096148521706100183)
                ·
                  refine ⟨11855610144222782559150275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7903740096148521706100183 11855610144222782559150275)
                  ·
                    refine ⟨17783415216334173838725413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11855610144222782559150275 17783415216334173838725413)
                    ·
                      refine ⟨3334390353062657594761015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17783415216334173838725413 3334390353062657594761015)
                      ·
                        rfl

theorem cell23_6493702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_6493702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493702 prefixEnd_6493702 := by exact prefixLift 6493702
  have htrace : WordTrace (prefixWord ++ tailWord_6493702) baseStart_6493702 baseEnd_6493702 := by
    simpa [prefixWord, tailWord_6493702, baseEnd_6493702] using wordTrace_append hprefix tailTrace_6493702
  have hstable : (prefixWord ++ tailWord_6493702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493702).length < 2 ^ (prefixWord ++ tailWord_6493702).sum := by decide
  have hdescent : baseEnd_6493702 < baseStart_6493702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493777 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 2, 5]
def baseStart_6493777 : Nat := 118140960795 + 6493777 * 2 ^ 59
def prefixEnd_6493777 : Nat := 4983230072969 + 3 ^ 40 * 6493777 * 2
def baseEnd_6493777 : Nat := 1111476288037248267107723

theorem tailTrace_6493777 : CollatzResearch.WordTrace tailWord_6493777 prefixEnd_6493777 1111476288037248267107723 := by
  unfold tailWord_6493777
  simp only [CollatzResearch.WordTrace]
  refine ⟨236847504995162452660823585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157898336663441635107215723 236847504995162452660823585)
  ·
    refine ⟨177635628746371839495617689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236847504995162452660823585 177635628746371839495617689)
    ·
      refine ⟨133226721559778879621713267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177635628746371839495617689 133226721559778879621713267)
      ·
        refine ⟨199840082339668319432569901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133226721559778879621713267 199840082339668319432569901)
        ·
          refine ⟨74940030877375619787213713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199840082339668319432569901 74940030877375619787213713)
          ·
            refine ⟨56205023158031714840410285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74940030877375619787213713 56205023158031714840410285)
            ·
              refine ⟨21076883684261893065153857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56205023158031714840410285 21076883684261893065153857)
              ·
                refine ⟨15807662763196419798865393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21076883684261893065153857 15807662763196419798865393)
                ·
                  refine ⟨11855747072397314849149045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15807662763196419798865393 11855747072397314849149045)
                  ·
                    refine ⟨1111476288037248267107723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11855747072397314849149045 1111476288037248267107723)
                    ·
                      rfl

theorem cell23_6493777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_6493777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493777 prefixEnd_6493777 := by exact prefixLift 6493777
  have htrace : WordTrace (prefixWord ++ tailWord_6493777) baseStart_6493777 baseEnd_6493777 := by
    simpa [prefixWord, tailWord_6493777, baseEnd_6493777] using wordTrace_append hprefix tailTrace_6493777
  have hstable : (prefixWord ++ tailWord_6493777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493777).length < 2 ^ (prefixWord ++ tailWord_6493777).sum := by decide
  have hdescent : baseEnd_6493777 < baseStart_6493777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493807 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 5, 4]
def baseStart_6493807 : Nat := 118140960795 + 6493807 * 2 ^ 59
def prefixEnd_6493807 : Nat := 4983230072969 + 3 ^ 40 * 6493807 * 2
def baseEnd_6493807 : Nat := 1111481422843793227982677

theorem tailTrace_6493807 : CollatzResearch.WordTrace tailWord_6493807 prefixEnd_6493807 1111481422843793227982677 := by
  unfold tailWord_6493807
  simp only [CollatzResearch.WordTrace]
  refine ⟨236848599185053767784415675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157899066123369178522943783 236848599185053767784415675)
  ·
    refine ⟨355272898777580651676623513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236848599185053767784415675 355272898777580651676623513)
    ·
      refine ⟨266454674083185488757467635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355272898777580651676623513 266454674083185488757467635)
      ·
        refine ⟨399682011124778233136201453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266454674083185488757467635 399682011124778233136201453)
        ·
          refine ⟨149880754171791837426075545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 399682011124778233136201453 149880754171791837426075545)
          ·
            refine ⟨112410565628843878069556659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149880754171791837426075545 112410565628843878069556659)
            ·
              refine ⟨168615848443265817104334989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112410565628843878069556659 168615848443265817104334989)
              ·
                refine ⟨63230943166224681414125621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168615848443265817104334989 63230943166224681414125621)
                ·
                  refine ⟨5927900921833563882574277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63230943166224681414125621 5927900921833563882574277)
                  ·
                    refine ⟨1111481422843793227982677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5927900921833563882574277 1111481422843793227982677)
                    ·
                      rfl

theorem cell23_6493807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 4].length) (baseStart_6493807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493807 prefixEnd_6493807 := by exact prefixLift 6493807
  have htrace : WordTrace (prefixWord ++ tailWord_6493807) baseStart_6493807 baseEnd_6493807 := by
    simpa [prefixWord, tailWord_6493807, baseEnd_6493807] using wordTrace_append hprefix tailTrace_6493807
  have hstable : (prefixWord ++ tailWord_6493807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493807).length < 2 ^ (prefixWord ++ tailWord_6493807).sum := by decide
  have hdescent : baseEnd_6493807 < baseStart_6493807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493858 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_6493858 : Nat := 118140960795 + 6493858 * 2 ^ 59
def prefixEnd_6493858 : Nat := 4983230072969 + 3 ^ 40 * 6493858 * 2
def baseEnd_6493858 : Nat := 1111490152014919661470099

theorem tailTrace_6493858 : CollatzResearch.WordTrace tailWord_6493858 prefixEnd_6493858 1111490152014919661470099 := by
  unfold tailWord_6493858
  simp only [CollatzResearch.WordTrace]
  refine ⟨59212614826967250873630557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157900306205246002329681485 59212614826967250873630557)
  ·
    refine ⟨22204730560112719077611459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59212614826967250873630557 22204730560112719077611459)
    ·
      refine ⟨33307095840169078616417189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22204730560112719077611459 33307095840169078616417189)
      ·
        refine ⟨6245080470031702240578223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33307095840169078616417189 6245080470031702240578223)
        ·
          refine ⟨9367620705047553360867335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6245080470031702240578223 9367620705047553360867335)
          ·
            refine ⟨14051431057571330041301003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9367620705047553360867335 14051431057571330041301003)
            ·
              refine ⟨21077146586356995061951505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14051431057571330041301003 21077146586356995061951505)
              ·
                refine ⟨15807859939767746296463629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21077146586356995061951505 15807859939767746296463629)
                ·
                  refine ⟨5927947477412904861173861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15807859939767746296463629 5927947477412904861173861)
                  ·
                    refine ⟨1111490152014919661470099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5927947477412904861173861 1111490152014919661470099)
                    ·
                      rfl

theorem cell23_6493858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_6493858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493858 prefixEnd_6493858 := by exact prefixLift 6493858
  have htrace : WordTrace (prefixWord ++ tailWord_6493858) baseStart_6493858 baseEnd_6493858 := by
    simpa [prefixWord, tailWord_6493858, baseEnd_6493858] using wordTrace_append hprefix tailTrace_6493858
  have hstable : (prefixWord ++ tailWord_6493858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493858).length < 2 ^ (prefixWord ++ tailWord_6493858).sum := by decide
  have hdescent : baseEnd_6493858 < baseStart_6493858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493898 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 3, 1, 3]
def baseStart_6493898 : Nat := 118140960795 + 6493898 * 2 ^ 59
def prefixEnd_6493898 : Nat := 4983230072969 + 3 ^ 40 * 6493898 * 2
def baseEnd_6493898 : Nat := 3334490995270938827910113

theorem tailTrace_6493898 : CollatzResearch.WordTrace tailWord_6493898 prefixEnd_6493898 3334490995270938827910113 := by
  unfold tailWord_6493898
  simp only [CollatzResearch.WordTrace]
  refine ⟨59212979556931022581494587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157901278818482726883985565 59212979556931022581494587)
  ·
    refine ⟨88819469335396533872241881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59212979556931022581494587 88819469335396533872241881)
    ·
      refine ⟨66614602001547400404181411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88819469335396533872241881 66614602001547400404181411)
      ·
        refine ⟨99921903002321100606272117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66614602001547400404181411 99921903002321100606272117)
        ·
          refine ⟨9367678406467603181838011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 99921903002321100606272117 9367678406467603181838011)
          ·
            refine ⟨14051517609701404772757017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9367678406467603181838011 14051517609701404772757017)
            ·
              refine ⟨10538638207276053579567763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14051517609701404772757017 10538638207276053579567763)
              ·
                refine ⟨15807957310914080369351645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10538638207276053579567763 15807957310914080369351645)
                ·
                  refine ⟨5927983991592780138506867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15807957310914080369351645 5927983991592780138506867)
                  ·
                    refine ⟨8891975987389170207760301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5927983991592780138506867 8891975987389170207760301)
                    ·
                      refine ⟨3334490995270938827910113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8891975987389170207760301 3334490995270938827910113)
                      ·
                        rfl

theorem cell23_6493898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 3, 1, 3].length) (baseStart_6493898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493898 prefixEnd_6493898 := by exact prefixLift 6493898
  have htrace : WordTrace (prefixWord ++ tailWord_6493898) baseStart_6493898 baseEnd_6493898 := by
    simpa [prefixWord, tailWord_6493898, baseEnd_6493898] using wordTrace_append hprefix tailTrace_6493898
  have hstable : (prefixWord ++ tailWord_6493898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493898).length < 2 ^ (prefixWord ++ tailWord_6493898).sum := by decide
  have hdescent : baseEnd_6493898 < baseStart_6493898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493914 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 1, 6]
def baseStart_6493914 : Nat := 118140960795 + 6493914 * 2 ^ 59
def prefixEnd_6493914 : Nat := 4983230072969 + 3 ^ 40 * 6493914 * 2
def baseEnd_6493914 : Nat := 1111499736987136921770013

theorem tailTrace_6493914 : CollatzResearch.WordTrace tailWord_6493914 prefixEnd_6493914 1111499736987136921770013 := by
  unfold tailWord_6493914
  simp only [CollatzResearch.WordTrace]
  refine ⟨59213125448916531264640199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157901667863777416705707197 59213125448916531264640199)
  ·
    refine ⟨88819688173374796896960299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59213125448916531264640199 88819688173374796896960299)
    ·
      refine ⟨133229532260062195345440449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88819688173374796896960299 133229532260062195345440449)
      ·
        refine ⟨99922149195046646509080337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133229532260062195345440449 99922149195046646509080337)
        ·
          refine ⟨74941611896284984881810253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 99922149195046646509080337 74941611896284984881810253)
          ·
            refine ⟨28103104461106869330678845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74941611896284984881810253 28103104461106869330678845)
            ·
              refine ⟨10538664172915075999004567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28103104461106869330678845 10538664172915075999004567)
              ·
                refine ⟨15807996259372613998506851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10538664172915075999004567 15807996259372613998506851)
                ·
                  refine ⟨23711994389058920997760277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15807996259372613998506851 23711994389058920997760277)
                  ·
                    refine ⟨1111499736987136921770013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23711994389058920997760277 1111499736987136921770013)
                    ·
                      rfl

theorem cell23_6493914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_6493914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493914 prefixEnd_6493914 := by exact prefixLift 6493914
  have htrace : WordTrace (prefixWord ++ tailWord_6493914) baseStart_6493914 baseEnd_6493914 := by
    simpa [prefixWord, tailWord_6493914, baseEnd_6493914] using wordTrace_append hprefix tailTrace_6493914
  have hstable : (prefixWord ++ tailWord_6493914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493914).length < 2 ^ (prefixWord ++ tailWord_6493914).sum := by decide
  have hdescent : baseEnd_6493914 < baseStart_6493914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493934 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4]
def baseStart_6493934 : Nat := 118140960795 + 6493934 * 2 ^ 59
def prefixEnd_6493934 : Nat := 4983230072969 + 3 ^ 40 * 6493934 * 2
def baseEnd_6493934 : Nat := 3334509480574500687059947

theorem tailTrace_6493934 : CollatzResearch.WordTrace tailWord_6493934 prefixEnd_6493934 3334509480574500687059947 := by
  unfold tailWord_6493934
  simp only [CollatzResearch.WordTrace]
  refine ⟨29606653906949208559286107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157902154170395778982859237 29606653906949208559286107)
  ·
    refine ⟨44409980860423812838929161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29606653906949208559286107 44409980860423812838929161)
    ·
      refine ⟨33307485645317859629196871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44409980860423812838929161 33307485645317859629196871)
      ·
        refine ⟨49961228467976789443795307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33307485645317859629196871 49961228467976789443795307)
        ·
          refine ⟨74941842701965184165692961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49961228467976789443795307 74941842701965184165692961)
          ·
            refine ⟨56206382026473888124269721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74941842701965184165692961 56206382026473888124269721)
            ·
              refine ⟨42154786519855416093202291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56206382026473888124269721 42154786519855416093202291)
              ·
                refine ⟨63232179779783124139803437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42154786519855416093202291 63232179779783124139803437)
                ·
                  refine ⟨23712067417418671552426289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63232179779783124139803437 23712067417418671552426289)
                  ·
                    refine ⟨17784050563064003664319717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23712067417418671552426289 17784050563064003664319717)
                    ·
                      refine ⟨3334509480574500687059947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17784050563064003664319717 3334509480574500687059947)
                      ·
                        rfl

theorem cell23_6493934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_6493934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493934 prefixEnd_6493934 := by exact prefixLift 6493934
  have htrace : WordTrace (prefixWord ++ tailWord_6493934) baseStart_6493934 baseEnd_6493934 := by
    simpa [prefixWord, tailWord_6493934, baseEnd_6493934] using wordTrace_append hprefix tailTrace_6493934
  have hstable : (prefixWord ++ tailWord_6493934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493934).length < 2 ^ (prefixWord ++ tailWord_6493934).sum := by decide
  have hdescent : baseEnd_6493934 < baseStart_6493934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6493967 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 5]
def baseStart_6493967 : Nat := 118140960795 + 6493967 * 2 ^ 59
def prefixEnd_6493967 : Nat := 4983230072969 + 3 ^ 40 * 6493967 * 2
def baseEnd_6493967 : Nat := 3334526425436099057947295

theorem tailTrace_6493967 : CollatzResearch.WordTrace tailWord_6493967 prefixEnd_6493967 3334526425436099057947295 := by
  unfold tailWord_6493967
  simp only [CollatzResearch.WordTrace]
  refine ⟨236854434864474115110240155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157902956576316076740160103 236854434864474115110240155)
  ·
    refine ⟨355281652296711172665360233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236854434864474115110240155 355281652296711172665360233)
    ·
      refine ⟨266461239222533379499020175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355281652296711172665360233 266461239222533379499020175)
      ·
        refine ⟨399691858833800069248530263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266461239222533379499020175 399691858833800069248530263)
        ·
          refine ⟨599537788250700103872795395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399691858833800069248530263 599537788250700103872795395)
          ·
            refine ⟨899306682376050155809193093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599537788250700103872795395 899306682376050155809193093)
            ·
              refine ⟨168620002945509404214223705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 899306682376050155809193093 168620002945509404214223705)
              ·
                refine ⟨126465002209132053160667779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168620002945509404214223705 126465002209132053160667779)
                ·
                  refine ⟨189697503313698079741001669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126465002209132053160667779 189697503313698079741001669)
                  ·
                    refine ⟨35568281871318389951437813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 189697503313698079741001669 35568281871318389951437813)
                    ·
                      refine ⟨3334526425436099057947295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35568281871318389951437813 3334526425436099057947295)
                      ·
                        rfl

theorem cell23_6493967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_6493967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6493967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6493967 prefixEnd_6493967 := by exact prefixLift 6493967
  have htrace : WordTrace (prefixWord ++ tailWord_6493967) baseStart_6493967 baseEnd_6493967 := by
    simpa [prefixWord, tailWord_6493967, baseEnd_6493967] using wordTrace_append hprefix tailTrace_6493967
  have hstable : (prefixWord ++ tailWord_6493967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6493967).length < 2 ^ (prefixWord ++ tailWord_6493967).sum := by decide
  have hdescent : baseEnd_6493967 < baseStart_6493967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6493967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494005 : List Nat := [1, 3, 3, 1, 4, 1, 2, 2, 2, 1, 3]
def baseStart_6494005 : Nat := 118140960795 + 6494005 * 2 ^ 59
def prefixEnd_6494005 : Nat := 4983230072969 + 3 ^ 40 * 6494005 * 2
def baseEnd_6494005 : Nat := 3334545937700969909272121

theorem tailTrace_6494005 : CollatzResearch.WordTrace tailWord_6494005 prefixEnd_6494005 3334545937700969909272121 := by
  unfold tailWord_6494005
  simp only [CollatzResearch.WordTrace]
  refine ⟨236855820838336447600123469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157903880558890965066748979 236855820838336447600123469)
  ·
    refine ⟨88820932814376167850046301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236855820838336447600123469 88820932814376167850046301)
    ·
      refine ⟨33307849805391062943767363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88820932814376167850046301 33307849805391062943767363)
      ·
        refine ⟨49961774708086594415651045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33307849805391062943767363 49961774708086594415651045)
        ·
          refine ⟨9367832757766236452934571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49961774708086594415651045 9367832757766236452934571)
          ·
            refine ⟨14051749136649354679401857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9367832757766236452934571 14051749136649354679401857)
            ·
              refine ⟨10538811852487016009551393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14051749136649354679401857 10538811852487016009551393)
              ·
                refine ⟨7904108889365262007163545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10538811852487016009551393 7904108889365262007163545)
                ·
                  refine ⟨5928081667023946505372659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7904108889365262007163545 5928081667023946505372659)
                  ·
                    refine ⟨8892122500535919758058989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5928081667023946505372659 8892122500535919758058989)
                    ·
                      refine ⟨3334545937700969909272121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8892122500535919758058989 3334545937700969909272121)
                      ·
                        rfl

theorem cell23_6494005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_6494005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494005 prefixEnd_6494005 := by exact prefixLift 6494005
  have htrace : WordTrace (prefixWord ++ tailWord_6494005) baseStart_6494005 baseEnd_6494005 := by
    simpa [prefixWord, tailWord_6494005, baseEnd_6494005] using wordTrace_append hprefix tailTrace_6494005
  have hstable : (prefixWord ++ tailWord_6494005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494005).length < 2 ^ (prefixWord ++ tailWord_6494005).sum := by decide
  have hdescent : baseEnd_6494005 < baseStart_6494005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494006 : List Nat := [5, 1, 2, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_6494006 : Nat := 118140960795 + 6494006 * 2 ^ 59
def prefixEnd_6494006 : Nat := 4983230072969 + 3 ^ 40 * 6494006 * 2
def baseEnd_6494006 : Nat := 3334546451181624405359617

theorem tailTrace_6494006 : CollatzResearch.WordTrace tailWord_6494006 prefixEnd_6494006 3334546451181624405359617 := by
  unfold tailWord_6494006
  simp only [CollatzResearch.WordTrace]
  refine ⟨14803491081958301548181867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157903904874221883180606581 14803491081958301548181867)
  ·
    refine ⟨22205236622937452322272801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14803491081958301548181867 22205236622937452322272801)
    ·
      refine ⟨16653927467203089241704601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22205236622937452322272801 16653927467203089241704601)
      ·
        refine ⟨12490445600402316931278451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16653927467203089241704601 12490445600402316931278451)
        ·
          refine ⟨18735668400603475396917677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12490445600402316931278451 18735668400603475396917677)
          ·
            refine ⟨7025875650226303273844129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18735668400603475396917677 7025875650226303273844129)
            ·
              refine ⟨5269406737669727455383097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7025875650226303273844129 5269406737669727455383097)
              ·
                refine ⟨3952055053252295591537323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5269406737669727455383097 3952055053252295591537323)
                ·
                  refine ⟨5928082579878443387305985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3952055053252295591537323 5928082579878443387305985)
                  ·
                    refine ⟨4446061934908832540479489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5928082579878443387305985 4446061934908832540479489)
                    ·
                      refine ⟨3334546451181624405359617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446061934908832540479489 3334546451181624405359617)
                      ·
                        rfl

theorem cell23_6494006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_6494006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494006 prefixEnd_6494006 := by exact prefixLift 6494006
  have htrace : WordTrace (prefixWord ++ tailWord_6494006) baseStart_6494006 baseEnd_6494006 := by
    simpa [prefixWord, tailWord_6494006, baseEnd_6494006] using wordTrace_append hprefix tailTrace_6494006
  have hstable : (prefixWord ++ tailWord_6494006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494006).length < 2 ^ (prefixWord ++ tailWord_6494006).sum := by decide
  have hdescent : baseEnd_6494006 < baseStart_6494006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494022 : List Nat := [6, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_6494022 : Nat := 118140960795 + 6494022 * 2 ^ 59
def prefixEnd_6494022 : Nat := 4983230072969 + 3 ^ 40 * 6494022 * 2
def baseEnd_6494022 : Nat := 3334554666872096342759543

theorem tailTrace_6494022 : CollatzResearch.WordTrace tailWord_6494022 prefixEnd_6494022 3334554666872096342759543 := by
  unfold tailWord_6494022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7401763777477339359484135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 157904293919516573002328213 7401763777477339359484135)
  ·
    refine ⟨11102645666216009039226203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7401763777477339359484135 11102645666216009039226203)
    ·
      refine ⟨16653968499324013558839305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11102645666216009039226203 16653968499324013558839305)
      ·
        refine ⟨12490476374493010169129479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16653968499324013558839305 12490476374493010169129479)
        ·
          refine ⟨18735714561739515253694219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12490476374493010169129479 18735714561739515253694219)
          ·
            refine ⟨28103571842609272880541329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18735714561739515253694219 28103571842609272880541329)
            ·
              refine ⟨21077678881956954660405997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28103571842609272880541329 21077678881956954660405997)
              ·
                refine ⟨7904129580733857997652249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21077678881956954660405997 7904129580733857997652249)
                ·
                  refine ⟨5928097185550393498239187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7904129580733857997652249 5928097185550393498239187)
                  ·
                    refine ⟨8892145778325590247358781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5928097185550393498239187 8892145778325590247358781)
                    ·
                      refine ⟨3334554666872096342759543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8892145778325590247358781 3334554666872096342759543)
                      ·
                        rfl

theorem cell23_6494022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_6494022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494022 prefixEnd_6494022 := by exact prefixLift 6494022
  have htrace : WordTrace (prefixWord ++ tailWord_6494022) baseStart_6494022 baseEnd_6494022 := by
    simpa [prefixWord, tailWord_6494022, baseEnd_6494022] using wordTrace_append hprefix tailTrace_6494022
  have hstable : (prefixWord ++ tailWord_6494022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494022).length < 2 ^ (prefixWord ++ tailWord_6494022).sum := by decide
  have hdescent : baseEnd_6494022 < baseStart_6494022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494024 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_6494024 : Nat := 118140960795 + 6494024 * 2 ^ 59
def prefixEnd_6494024 : Nat := 4983230072969 + 3 ^ 40 * 6494024 * 2
def baseEnd_6494024 : Nat := 3334555693833405334934533

theorem tailTrace_6494024 : CollatzResearch.WordTrace tailWord_6494024 prefixEnd_6494024 3334555693833405334934533 := by
  unfold tailWord_6494024
  simp only [CollatzResearch.WordTrace]
  refine ⟨118428256912633806922532563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157904342550178409230043417 118428256912633806922532563)
  ·
    refine ⟨177642385368950710383798845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118428256912633806922532563 177642385368950710383798845)
    ·
      refine ⟨66615894513356516393924567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177642385368950710383798845 66615894513356516393924567)
      ·
        refine ⟨99923841770034774590886851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66615894513356516393924567 99923841770034774590886851)
        ·
          refine ⟨149885762655052161886330277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99923841770034774590886851 149885762655052161886330277)
          ·
            refine ⟨28103580497822280353686927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149885762655052161886330277 28103580497822280353686927)
            ·
              refine ⟨42155370746733420530530391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28103580497822280353686927 42155370746733420530530391)
              ·
                refine ⟨63233056120100130795795587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42155370746733420530530391 63233056120100130795795587)
                ·
                  refine ⟨94849584180150196193693381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63233056120100130795795587 94849584180150196193693381)
                  ·
                    refine ⟨17784297033778161786317509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94849584180150196193693381 17784297033778161786317509)
                    ·
                      refine ⟨3334555693833405334934533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17784297033778161786317509 3334555693833405334934533)
                      ·
                        rfl

theorem cell23_6494024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_6494024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494024 prefixEnd_6494024 := by exact prefixLift 6494024
  have htrace : WordTrace (prefixWord ++ tailWord_6494024) baseStart_6494024 baseEnd_6494024 := by
    simpa [prefixWord, tailWord_6494024, baseEnd_6494024] using wordTrace_append hprefix tailTrace_6494024
  have hstable : (prefixWord ++ tailWord_6494024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494024).length < 2 ^ (prefixWord ++ tailWord_6494024).sum := by decide
  have hdescent : baseEnd_6494024 < baseStart_6494024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494034 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 9]
def baseStart_6494034 : Nat := 118140960795 + 6494034 * 2 ^ 59
def prefixEnd_6494034 : Nat := 4983230072969 + 3 ^ 40 * 6494034 * 2
def baseEnd_6494034 : Nat := 370506758737772255089943

theorem tailTrace_6494034 : CollatzResearch.WordTrace tailWord_6494034 prefixEnd_6494034 370506758737772255089943 := by
  unfold tailWord_6494034
  simp only [CollatzResearch.WordTrace]
  refine ⟨59214219638807846388232289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157904585703487590368619437 59214219638807846388232289)
  ·
    refine ⟨44410664729105884791174217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59214219638807846388232289 44410664729105884791174217)
    ·
      refine ⟨33307998546829413593380663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44410664729105884791174217 33307998546829413593380663)
      ·
        refine ⟨49961997820244120390070995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33307998546829413593380663 49961997820244120390070995)
        ·
          refine ⟨74942996730366180585106493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49961997820244120390070995 74942996730366180585106493)
          ·
            refine ⟨28103623773887317719414935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74942996730366180585106493 28103623773887317719414935)
            ·
              refine ⟨42155435660830976579122403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28103623773887317719414935 42155435660830976579122403)
              ·
                refine ⟨63233153491246464868683605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42155435660830976579122403 63233153491246464868683605)
                ·
                  refine ⟨370506758737772255089943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63233153491246464868683605 370506758737772255089943)
                  ·
                    rfl

theorem cell23_6494034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_6494034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494034 prefixEnd_6494034 := by exact prefixLift 6494034
  have htrace : WordTrace (prefixWord ++ tailWord_6494034) baseStart_6494034 baseEnd_6494034 := by
    simpa [prefixWord, tailWord_6494034, baseEnd_6494034] using wordTrace_append hprefix tailTrace_6494034
  have hstable : (prefixWord ++ tailWord_6494034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494034).length < 2 ^ (prefixWord ++ tailWord_6494034).sum := by decide
  have hdescent : baseEnd_6494034 < baseStart_6494034 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494061 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 2, 3, 3]
def baseStart_6494061 : Nat := 118140960795 + 6494061 * 2 ^ 59
def prefixEnd_6494061 : Nat := 4983230072969 + 3 ^ 40 * 6494061 * 2
def baseEnd_6494061 : Nat := 3334574692617621690171863

theorem tailTrace_6494061 : CollatzResearch.WordTrace tailWord_6494061 prefixEnd_6494061 3334574692617621690171863 := by
  unfold tailWord_6494061
  simp only [CollatzResearch.WordTrace]
  refine ⟨236857863326133569164162037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157905242217422379442774691 236857863326133569164162037)
  ·
    refine ⟨22205424686825022109140191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 236857863326133569164162037 22205424686825022109140191)
    ·
      refine ⟨33308137030237533163710287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22205424686825022109140191 33308137030237533163710287)
      ·
        refine ⟨49962205545356299745565431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33308137030237533163710287 49962205545356299745565431)
        ·
          refine ⟨74943308318034449618348147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49962205545356299745565431 74943308318034449618348147)
          ·
            refine ⟨112414962477051674427522221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74943308318034449618348147 112414962477051674427522221)
            ·
              refine ⟨42155610928894377910320833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112414962477051674427522221 42155610928894377910320833)
              ·
                refine ⟨31616708196670783432740625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42155610928894377910320833 31616708196670783432740625)
                ·
                  refine ⟨23712531147503087574555469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31616708196670783432740625 23712531147503087574555469)
                  ·
                    refine ⟨8892199180313657840458301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23712531147503087574555469 8892199180313657840458301)
                    ·
                      refine ⟨3334574692617621690171863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8892199180313657840458301 3334574692617621690171863)
                      ·
                        rfl

theorem cell23_6494061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_6494061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494061 prefixEnd_6494061 := by exact prefixLift 6494061
  have htrace : WordTrace (prefixWord ++ tailWord_6494061) baseStart_6494061 baseEnd_6494061 := by
    simpa [prefixWord, tailWord_6494061, baseEnd_6494061] using wordTrace_append hprefix tailTrace_6494061
  have hstable : (prefixWord ++ tailWord_6494061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494061).length < 2 ^ (prefixWord ++ tailWord_6494061).sum := by decide
  have hdescent : baseEnd_6494061 < baseStart_6494061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494062 : List Nat := [4, 1, 2, 3, 1, 1, 3, 2, 2, 2, 2]
def baseStart_6494062 : Nat := 118140960795 + 6494062 * 2 ^ 59
def prefixEnd_6494062 : Nat := 4983230072969 + 3 ^ 40 * 6494062 * 2
def baseEnd_6494062 : Nat := 3334575206098276186259359

theorem tailTrace_6494062 : CollatzResearch.WordTrace tailWord_6494062 prefixEnd_6494062 3334575206098276186259359 := by
  unfold tailWord_6494062
  simp only [CollatzResearch.WordTrace]
  refine ⟨29607237474891243291868555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157905266532753297556632293 29607237474891243291868555)
  ·
    refine ⟨44410856212336864937802833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29607237474891243291868555 44410856212336864937802833)
    ·
      refine ⟨33308142159252648703352125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44410856212336864937802833 33308142159252648703352125)
      ·
        refine ⟨12490553309719743263757047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33308142159252648703352125 12490553309719743263757047)
        ·
          refine ⟨18735829964579614895635571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12490553309719743263757047 18735829964579614895635571)
          ·
            refine ⟨28103744946869422343453357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18735829964579614895635571 28103744946869422343453357)
            ·
              refine ⟨10538904355076033378795009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28103744946869422343453357 10538904355076033378795009)
              ·
                refine ⟨7904178266307025034096257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10538904355076033378795009 7904178266307025034096257)
                ·
                  refine ⟨5928133699730268775572193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7904178266307025034096257 5928133699730268775572193)
                  ·
                    refine ⟨4446100274797701581679145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5928133699730268775572193 4446100274797701581679145)
                    ·
                      refine ⟨3334575206098276186259359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446100274797701581679145 3334575206098276186259359)
                      ·
                        rfl

theorem cell23_6494062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_6494062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494062 prefixEnd_6494062 := by exact prefixLift 6494062
  have htrace : WordTrace (prefixWord ++ tailWord_6494062) baseStart_6494062 baseEnd_6494062 := by
    simpa [prefixWord, tailWord_6494062, baseEnd_6494062] using wordTrace_append hprefix tailTrace_6494062
  have hstable : (prefixWord ++ tailWord_6494062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494062).length < 2 ^ (prefixWord ++ tailWord_6494062).sum := by decide
  have hdescent : baseEnd_6494062 < baseStart_6494062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494064 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 4, 5]
def baseStart_6494064 : Nat := 118140960795 + 6494064 * 2 ^ 59
def prefixEnd_6494064 : Nat := 4983230072969 + 3 ^ 40 * 6494064 * 2
def baseEnd_6494064 : Nat := 1111525411019861726144783

theorem tailTrace_6494064 : CollatzResearch.WordTrace tailWord_6494064 prefixEnd_6494064 1111525411019861726144783 := by
  unfold tailWord_6494064
  simp only [CollatzResearch.WordTrace]
  refine ⟨118428986372561350338260623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157905315163415133784347497 118428986372561350338260623)
  ·
    refine ⟨177643479558842025507390935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118428986372561350338260623 177643479558842025507390935)
    ·
      refine ⟨266465219338263038261086403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177643479558842025507390935 266465219338263038261086403)
      ·
        refine ⟨399697829007394557391629605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266465219338263038261086403 399697829007394557391629605)
        ·
          refine ⟨74943342938886479510930551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 399697829007394557391629605 74943342938886479510930551)
          ·
            refine ⟨112415014408329719266395827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74943342938886479510930551 112415014408329719266395827)
            ·
              refine ⟨168622521612494578899593741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112415014408329719266395827 168622521612494578899593741)
              ·
                refine ⟨63233445604685467087347653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168622521612494578899593741 63233445604685467087347653)
                ·
                  refine ⟨11856271050878525078877685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63233445604685467087347653 11856271050878525078877685)
                  ·
                    refine ⟨1111525411019861726144783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11856271050878525078877685 1111525411019861726144783)
                    ·
                      rfl

theorem cell23_6494064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 4, 5].length) (baseStart_6494064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494064 prefixEnd_6494064 := by exact prefixLift 6494064
  have htrace : WordTrace (prefixWord ++ tailWord_6494064) baseStart_6494064 baseEnd_6494064 := by
    simpa [prefixWord, tailWord_6494064, baseEnd_6494064] using wordTrace_append hprefix tailTrace_6494064
  have hstable : (prefixWord ++ tailWord_6494064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494064).length < 2 ^ (prefixWord ++ tailWord_6494064).sum := by decide
  have hdescent : baseEnd_6494064 < baseStart_6494064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494074 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5]
def baseStart_6494074 : Nat := 118140960795 + 6494074 * 2 ^ 59
def prefixEnd_6494074 : Nat := 4983230072969 + 3 ^ 40 * 6494074 * 2
def baseEnd_6494074 : Nat := 3334581367866130139309303

theorem tailTrace_6494074 : CollatzResearch.WordTrace tailWord_6494074 prefixEnd_6494074 3334581367866130139309303 := by
  unfold tailWord_6494074
  simp only [CollatzResearch.WordTrace]
  refine ⟨59214584368771618096096319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157905558316724314922923517 59214584368771618096096319)
  ·
    refine ⟨88821876553157427144144479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59214584368771618096096319 88821876553157427144144479)
    ·
      refine ⟨133232814829736140716216719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88821876553157427144144479 133232814829736140716216719)
      ·
        refine ⟨199849222244604211074325079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133232814829736140716216719 199849222244604211074325079)
        ·
          refine ⟨299773833366906316611487619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199849222244604211074325079 299773833366906316611487619)
          ·
            refine ⟨449660750050359474917231429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299773833366906316611487619 449660750050359474917231429)
            ·
              refine ⟨84311390634442401546980893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 449660750050359474917231429 84311390634442401546980893)
              ·
                refine ⟨31616771487915900580117835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84311390634442401546980893 31616771487915900580117835)
                ·
                  refine ⟨47425157231873850870176753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31616771487915900580117835 47425157231873850870176753)
                  ·
                    refine ⟨35568867923905388152632565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47425157231873850870176753 35568867923905388152632565)
                    ·
                      refine ⟨3334581367866130139309303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35568867923905388152632565 3334581367866130139309303)
                      ·
                        rfl

theorem cell23_6494074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_6494074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494074 prefixEnd_6494074 := by exact prefixLift 6494074
  have htrace : WordTrace (prefixWord ++ tailWord_6494074) baseStart_6494074 baseEnd_6494074 := by
    simpa [prefixWord, tailWord_6494074, baseEnd_6494074] using wordTrace_append hprefix tailTrace_6494074
  have hstable : (prefixWord ++ tailWord_6494074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494074).length < 2 ^ (prefixWord ++ tailWord_6494074).sum := by decide
  have hdescent : baseEnd_6494074 < baseStart_6494074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494101 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 2, 1, 4]
def baseStart_6494101 : Nat := 118140960795 + 6494101 * 2 ^ 59
def prefixEnd_6494101 : Nat := 4983230072969 + 3 ^ 40 * 6494101 * 2
def baseEnd_6494101 : Nat := 3334595231843801533671679

theorem tailTrace_6494101 : CollatzResearch.WordTrace tailWord_6494101 prefixEnd_6494101 3334595231843801533671679 := by
  unfold tailWord_6494101
  simp only [CollatzResearch.WordTrace]
  refine ⟨236859322245988655995618157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157906214830659103997078771 236859322245988655995618157)
  ·
    refine ⟨88822245842245745998356809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236859322245988655995618157 88822245842245745998356809)
    ·
      refine ⟨66616684381684309498767607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88822245842245745998356809 66616684381684309498767607)
      ·
        refine ⟨99925026572526464248151411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66616684381684309498767607 99925026572526464248151411)
        ·
          refine ⟨149887539858789696372227117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99925026572526464248151411 149887539858789696372227117)
          ·
            refine ⟨56207827447046136139585169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149887539858789696372227117 56207827447046136139585169)
            ·
              refine ⟨42155870585284602104688877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56207827447046136139585169 42155870585284602104688877)
              ·
                refine ⟨15808451469481725789258329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42155870585284602104688877 15808451469481725789258329)
                ·
                  refine ⟨11856338602111294341943747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15808451469481725789258329 11856338602111294341943747)
                  ·
                    refine ⟨17784507903166941512915621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11856338602111294341943747 17784507903166941512915621)
                    ·
                      refine ⟨3334595231843801533671679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17784507903166941512915621 3334595231843801533671679)
                      ·
                        rfl

theorem cell23_6494101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_6494101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494101 prefixEnd_6494101 := by exact prefixLift 6494101
  have htrace : WordTrace (prefixWord ++ tailWord_6494101) baseStart_6494101 baseEnd_6494101 := by
    simpa [prefixWord, tailWord_6494101, baseEnd_6494101] using wordTrace_append hprefix tailTrace_6494101
  have hstable : (prefixWord ++ tailWord_6494101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494101).length < 2 ^ (prefixWord ++ tailWord_6494101).sum := by decide
  have hdescent : baseEnd_6494101 < baseStart_6494101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494191 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 4]
def baseStart_6494191 : Nat := 118140960795 + 6494191 * 2 ^ 59
def prefixEnd_6494191 : Nat := 4983230072969 + 3 ^ 40 * 6494191 * 2
def baseEnd_6494191 : Nat := 3334641445102706181546265

theorem tailTrace_6494191 : CollatzResearch.WordTrace tailWord_6494191 prefixEnd_6494191 3334641445102706181546265 := by
  unfold tailWord_6494191
  simp only [CollatzResearch.WordTrace]
  refine ⟨236862604815662601366394427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157908403210441734244262951 236862604815662601366394427)
  ·
    refine ⟨355293907223493902049591641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236862604815662601366394427 355293907223493902049591641)
    ·
      refine ⟨266470430417620426537193731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355293907223493902049591641 266470430417620426537193731)
      ·
        refine ⟨399705645626430639805790597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266470430417620426537193731 399705645626430639805790597)
        ·
          refine ⟨74944808554955744963585737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 399705645626430639805790597 74944808554955744963585737)
          ·
            refine ⟨56208606416216808722689303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74944808554955744963585737 56208606416216808722689303)
            ·
              refine ⟨84312909624325213084033955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56208606416216808722689303 84312909624325213084033955)
              ·
                refine ⟨126469364436487819626050933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84312909624325213084033955 126469364436487819626050933)
                ·
                  refine ⟨11856502915920733089942275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126469364436487819626050933 11856502915920733089942275)
                  ·
                    refine ⟨17784754373881099634913413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11856502915920733089942275 17784754373881099634913413)
                    ·
                      refine ⟨3334641445102706181546265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17784754373881099634913413 3334641445102706181546265)
                      ·
                        rfl

theorem cell23_6494191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 1, 4].length) (baseStart_6494191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494191 prefixEnd_6494191 := by exact prefixLift 6494191
  have htrace : WordTrace (prefixWord ++ tailWord_6494191) baseStart_6494191 baseEnd_6494191 := by
    simpa [prefixWord, tailWord_6494191, baseEnd_6494191] using wordTrace_append hprefix tailTrace_6494191
  have hstable : (prefixWord ++ tailWord_6494191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494191).length < 2 ^ (prefixWord ++ tailWord_6494191).sum := by decide
  have hdescent : baseEnd_6494191 < baseStart_6494191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494201 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 1, 6]
def baseStart_6494201 : Nat := 118140960795 + 6494201 * 2 ^ 59
def prefixEnd_6494201 : Nat := 4983230072969 + 3 ^ 40 * 6494201 * 2
def baseEnd_6494201 : Nat := 1111548859969750380807073

theorem tailTrace_6494201 : CollatzResearch.WordTrace tailWord_6494201 prefixEnd_6494201 1111548859969750380807073 := by
  unfold tailWord_6494201
  simp only [CollatzResearch.WordTrace]
  refine ⟨236862969545626373074258457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157908646363750915382838971 236862969545626373074258457)
  ·
    refine ⟨177647227159219779805693843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236862969545626373074258457 177647227159219779805693843)
    ·
      refine ⟨266470840738829669708540765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177647227159219779805693843 266470840738829669708540765)
      ·
        refine ⟨99926565277061126140702787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266470840738829669708540765 99926565277061126140702787)
        ·
          refine ⟨149889847915591689211054181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99926565277061126140702787 149889847915591689211054181)
          ·
            refine ⟨28104346484173441727072659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 149889847915591689211054181 28104346484173441727072659)
            ·
              refine ⟨42156519726260162590608989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28104346484173441727072659 42156519726260162590608989)
              ·
                refine ⟨15808694897347560971478371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42156519726260162590608989 15808694897347560971478371)
                ·
                  refine ⟨23713042346021341457217557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15808694897347560971478371 23713042346021341457217557)
                  ·
                    refine ⟨1111548859969750380807073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23713042346021341457217557 1111548859969750380807073)
                    ·
                      rfl

theorem cell23_6494201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 6].length) (baseStart_6494201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494201 prefixEnd_6494201 := by exact prefixLift 6494201
  have htrace : WordTrace (prefixWord ++ tailWord_6494201) baseStart_6494201 baseEnd_6494201 := by
    simpa [prefixWord, tailWord_6494201, baseEnd_6494201] using wordTrace_append hprefix tailTrace_6494201
  have hstable : (prefixWord ++ tailWord_6494201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494201).length < 2 ^ (prefixWord ++ tailWord_6494201).sum := by decide
  have hdescent : baseEnd_6494201 < baseStart_6494201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494212 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 1, 5, 2]
def baseStart_6494212 : Nat := 118140960795 + 6494212 * 2 ^ 59
def prefixEnd_6494212 : Nat := 4983230072969 + 3 ^ 40 * 6494212 * 2
def baseEnd_6494212 : Nat := 3334652228196450599383669

theorem tailTrace_6494212 : CollatzResearch.WordTrace tailWord_6494212 prefixEnd_6494212 3334652228196450599383669 := by
  unfold tailWord_6494212
  simp only [CollatzResearch.WordTrace]
  refine ⟨118431685374293260976454445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157908913832391014635272593 118431685374293260976454445)
  ·
    refine ⟨44411882015359972866170417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118431685374293260976454445 44411882015359972866170417)
    ·
      refine ⟨33308911511519979649627813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44411882015359972866170417 33308911511519979649627813)
      ·
        refine ⟨6245420908409996184305215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33308911511519979649627813 6245420908409996184305215)
        ·
          refine ⟨9368131362614994276457823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6245420908409996184305215 9368131362614994276457823)
          ·
            refine ⟨14052197043922491414686735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9368131362614994276457823 14052197043922491414686735)
            ·
              refine ⟨21078295565883737122030103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14052197043922491414686735 21078295565883737122030103)
              ·
                refine ⟨31617443348825605683045155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21078295565883737122030103 31617443348825605683045155)
                ·
                  refine ⟨47426165023238408524567733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31617443348825605683045155 47426165023238408524567733)
                  ·
                    refine ⟨4446202970928600799178225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47426165023238408524567733 4446202970928600799178225)
                    ·
                      refine ⟨3334652228196450599383669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446202970928600799178225 3334652228196450599383669)
                      ·
                        rfl

theorem cell23_6494212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_6494212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494212 prefixEnd_6494212 := by exact prefixLift 6494212
  have htrace : WordTrace (prefixWord ++ tailWord_6494212) baseStart_6494212 baseEnd_6494212 := by
    simpa [prefixWord, tailWord_6494212, baseEnd_6494212] using wordTrace_append hprefix tailTrace_6494212
  have hstable : (prefixWord ++ tailWord_6494212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494212).length < 2 ^ (prefixWord ++ tailWord_6494212).sum := by decide
  have hdescent : baseEnd_6494212 < baseStart_6494212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494242 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 3, 2, 2]
def baseStart_6494242 : Nat := 118140960795 + 6494242 * 2 ^ 59
def prefixEnd_6494242 : Nat := 4983230072969 + 3 ^ 40 * 6494242 * 2
def baseEnd_6494242 : Nat := 3334667632616085482008531

theorem tailTrace_6494242 : CollatzResearch.WordTrace tailWord_6494242 prefixEnd_6494242 3334667632616085482008531 := by
  unfold tailWord_6494242
  simp only [CollatzResearch.WordTrace]
  refine ⟨59216116234619459269125245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157909643292318558051000653 59216116234619459269125245)
  ·
    refine ⟨22206043587982297225921967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59216116234619459269125245 22206043587982297225921967)
    ·
      refine ⟨33309065381973445838882951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22206043587982297225921967 33309065381973445838882951)
      ·
        refine ⟨49963598072960168758324427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33309065381973445838882951 49963598072960168758324427)
        ·
          refine ⟨74945397109440253137486641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49963598072960168758324427 74945397109440253137486641)
          ·
            refine ⟨56209047832080189853114981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74945397109440253137486641 56209047832080189853114981)
            ·
              refine ⟨10539196468515035597459059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56209047832080189853114981 10539196468515035597459059)
              ·
                refine ⟨15808794702772553396188589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10539196468515035597459059 15808794702772553396188589)
                ·
                  refine ⟨5928298013539707523570721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15808794702772553396188589 5928298013539707523570721)
                  ·
                    refine ⟨4446223510154780642678041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5928298013539707523570721 4446223510154780642678041)
                    ·
                      refine ⟨3334667632616085482008531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446223510154780642678041 3334667632616085482008531)
                      ·
                        rfl

theorem cell23_6494242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_6494242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494242 prefixEnd_6494242 := by exact prefixLift 6494242
  have htrace : WordTrace (prefixWord ++ tailWord_6494242) baseStart_6494242 baseEnd_6494242 := by
    simpa [prefixWord, tailWord_6494242, baseEnd_6494242] using wordTrace_append hprefix tailTrace_6494242
  have hstable : (prefixWord ++ tailWord_6494242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494242).length < 2 ^ (prefixWord ++ tailWord_6494242).sum := by decide
  have hdescent : baseEnd_6494242 < baseStart_6494242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494261 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 2, 7]
def baseStart_6494261 : Nat := 118140960795 + 6494261 * 2 ^ 59
def prefixEnd_6494261 : Nat := 4983230072969 + 3 ^ 40 * 6494261 * 2
def baseEnd_6494261 : Nat := 1111559129582840302556981

theorem tailTrace_6494261 : CollatzResearch.WordTrace tailWord_6494261 prefixEnd_6494261 1111559129582840302556981 := by
  unfold tailWord_6494261
  simp only [CollatzResearch.WordTrace]
  refine ⟨236865157925409003321442637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157910105283606002214295091 236865157925409003321442637)
  ·
    refine ⟨88824434222028376245540989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236865157925409003321442637 88824434222028376245540989)
    ·
      refine ⟨33309162833260641092077871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88824434222028376245540989 33309162833260641092077871)
      ·
        refine ⟨49963744249890961638116807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33309162833260641092077871 49963744249890961638116807)
        ·
          refine ⟨74945616374836442457175211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49963744249890961638116807 74945616374836442457175211)
          ·
            refine ⟨112418424562254663685762817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74945616374836442457175211 112418424562254663685762817)
            ·
              refine ⟨84313818421690997764322113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112418424562254663685762817 84313818421690997764322113)
              ·
                refine ⟨63235363816268248323241585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84313818421690997764322113 63235363816268248323241585)
                ·
                  refine ⟨47426522862201186242431189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63235363816268248323241585 47426522862201186242431189)
                  ·
                    refine ⟨1111559129582840302556981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47426522862201186242431189 1111559129582840302556981)
                    ·
                      rfl

theorem cell23_6494261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_6494261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494261 prefixEnd_6494261 := by exact prefixLift 6494261
  have htrace : WordTrace (prefixWord ++ tailWord_6494261) baseStart_6494261 baseEnd_6494261 := by
    simpa [prefixWord, tailWord_6494261, baseEnd_6494261] using wordTrace_append hprefix tailTrace_6494261
  have hstable : (prefixWord ++ tailWord_6494261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494261).length < 2 ^ (prefixWord ++ tailWord_6494261).sum := by decide
  have hdescent : baseEnd_6494261 < baseStart_6494261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494262 : List Nat := [5, 1, 2, 1, 1, 1, 4, 2, 1, 2, 3]
def baseStart_6494262 : Nat := 118140960795 + 6494262 * 2 ^ 59
def prefixEnd_6494262 : Nat := 4983230072969 + 3 ^ 40 * 6494262 * 2
def baseEnd_6494262 : Nat := 3334677902229175403758439

theorem tailTrace_6494262 : CollatzResearch.WordTrace tailWord_6494262 prefixEnd_6494262 3334677902229175403758439 := by
  unfold tailWord_6494262
  simp only [CollatzResearch.WordTrace]
  refine ⟨14804074649900336280764315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157910129598936920328152693 14804074649900336280764315)
  ·
    refine ⟨22206111974850504421146473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14804074649900336280764315 22206111974850504421146473)
    ·
      refine ⟨16654583981137878315859855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22206111974850504421146473 16654583981137878315859855)
      ·
        refine ⟨24981875971706817473789783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16654583981137878315859855 24981875971706817473789783)
        ·
          refine ⟨37472813957560226210684675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24981875971706817473789783 37472813957560226210684675)
          ·
            refine ⟨56209220936340339316027013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37472813957560226210684675 56209220936340339316027013)
            ·
              refine ⟨10539228925563813621755065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56209220936340339316027013 10539228925563813621755065)
              ·
                refine ⟨7904421694172860216316299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10539228925563813621755065 7904421694172860216316299)
                ·
                  refine ⟨11856632541259290324474449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7904421694172860216316299 11856632541259290324474449)
                  ·
                    refine ⟨8892474405944467743355837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11856632541259290324474449 8892474405944467743355837)
                    ·
                      refine ⟨3334677902229175403758439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8892474405944467743355837 3334677902229175403758439)
                      ·
                        rfl

theorem cell23_6494262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 2, 1, 2, 3].length) (baseStart_6494262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494262 prefixEnd_6494262 := by exact prefixLift 6494262
  have htrace : WordTrace (prefixWord ++ tailWord_6494262) baseStart_6494262 baseEnd_6494262 := by
    simpa [prefixWord, tailWord_6494262, baseEnd_6494262] using wordTrace_append hprefix tailTrace_6494262
  have hstable : (prefixWord ++ tailWord_6494262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494262).length < 2 ^ (prefixWord ++ tailWord_6494262).sum := by decide
  have hdescent : baseEnd_6494262 < baseStart_6494262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494265 : List Nat := [1, 2, 1, 5, 3, 2, 2, 7]
def baseStart_6494265 : Nat := 118140960795 + 6494265 * 2 ^ 59
def prefixEnd_6494265 : Nat := 4983230072969 + 3 ^ 40 * 6494265 * 2
def baseEnd_6494265 : Nat := 123506646024856996000775

theorem tailTrace_6494265 : CollatzResearch.WordTrace tailWord_6494265 prefixEnd_6494265 123506646024856996000775 := by
  unfold tailWord_6494265
  simp only [CollatzResearch.WordTrace]
  refine ⟨236865303817394512004588249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157910202544929674669725499 236865303817394512004588249)
  ·
    refine ⟨177648977863045884003441187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236865303817394512004588249 177648977863045884003441187)
    ·
      refine ⟨266473466794568826005161781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177648977863045884003441187 266473466794568826005161781)
      ·
        refine ⟨24981887511990827437983917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 266473466794568826005161781 24981887511990827437983917)
        ·
          refine ⟨9368207816996560289243969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24981887511990827437983917 9368207816996560289243969)
          ·
            refine ⟨7026155862747420216932977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9368207816996560289243969 7026155862747420216932977)
            ·
              refine ⟨5269616897060565162699733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7026155862747420216932977 5269616897060565162699733)
              ·
                refine ⟨123506646024856996000775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5269616897060565162699733 123506646024856996000775)
                ·
                  rfl

theorem cell23_6494265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 7].length) (baseStart_6494265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494265 prefixEnd_6494265 := by exact prefixLift 6494265
  have htrace : WordTrace (prefixWord ++ tailWord_6494265) baseStart_6494265 baseEnd_6494265 := by
    simpa [prefixWord, tailWord_6494265, baseEnd_6494265] using wordTrace_append hprefix tailTrace_6494265
  have hstable : (prefixWord ++ tailWord_6494265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494265).length < 2 ^ (prefixWord ++ tailWord_6494265).sum := by decide
  have hdescent : baseEnd_6494265 < baseStart_6494265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494271 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 5]
def baseStart_6494271 : Nat := 118140960795 + 6494271 * 2 ^ 59
def prefixEnd_6494271 : Nat := 4983230072969 + 3 ^ 40 * 6494271 * 2
def baseEnd_6494271 : Nat := 3334682523555065868545897

theorem tailTrace_6494271 : CollatzResearch.WordTrace tailWord_6494271 prefixEnd_6494271 3334682523555065868545897 := by
  unfold tailWord_6494271
  simp only [CollatzResearch.WordTrace]
  refine ⟨236865522655372775029306667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157910348436915183352871111 236865522655372775029306667)
  ·
    refine ⟨355298283983059162543960001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236865522655372775029306667 355298283983059162543960001)
    ·
      refine ⟨266473712987294371907970001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355298283983059162543960001 266473712987294371907970001)
      ·
        refine ⟨199855284740470778930977501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266473712987294371907970001 199855284740470778930977501)
        ·
          refine ⟨74945731777676542099116563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 199855284740470778930977501 74945731777676542099116563)
          ·
            refine ⟨112418597666514813148674845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74945731777676542099116563 112418597666514813148674845)
            ·
              refine ⟨42156974124943054930753067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112418597666514813148674845 42156974124943054930753067)
              ·
                refine ⟨63235461187414582396129601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42156974124943054930753067 63235461187414582396129601)
                ·
                  refine ⟨47426595890560936797097201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63235461187414582396129601 47426595890560936797097201)
                  ·
                    refine ⟨35569946917920702597822901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47426595890560936797097201 35569946917920702597822901)
                    ·
                      refine ⟨3334682523555065868545897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35569946917920702597822901 3334682523555065868545897)
                      ·
                        rfl

theorem cell23_6494271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_6494271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494271 prefixEnd_6494271 := by exact prefixLift 6494271
  have htrace : WordTrace (prefixWord ++ tailWord_6494271) baseStart_6494271 baseEnd_6494271 := by
    simpa [prefixWord, tailWord_6494271, baseEnd_6494271] using wordTrace_append hprefix tailTrace_6494271
  have hstable : (prefixWord ++ tailWord_6494271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494271).length < 2 ^ (prefixWord ++ tailWord_6494271).sum := by decide
  have hdescent : baseEnd_6494271 < baseStart_6494271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494309 : List Nat := [1, 3, 1, 3, 2, 4, 2, 1, 2, 1, 3]
def baseStart_6494309 : Nat := 118140960795 + 6494309 * 2 ^ 59
def prefixEnd_6494309 : Nat := 4983230072969 + 3 ^ 40 * 6494309 * 2
def baseEnd_6494309 : Nat := 3334702035819936719870723

theorem tailTrace_6494309 : CollatzResearch.WordTrace tailWord_6494309 prefixEnd_6494309 3334702035819936719870723 := by
  unfold tailWord_6494309
  simp only [CollatzResearch.WordTrace]
  refine ⟨236866908629235107519189981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157911272419490071679459987 236866908629235107519189981)
  ·
    refine ⟨88825090735963165319696243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236866908629235107519189981 88825090735963165319696243)
    ·
      refine ⟨133237636103944747979544365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88825090735963165319696243 133237636103944747979544365)
      ·
        refine ⟨49964113538979280492329137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133237636103944747979544365 49964113538979280492329137)
        ·
          refine ⟨37473085154234460369246853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49964113538979280492329137 37473085154234460369246853)
          ·
            refine ⟨7026203466418961319233785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37473085154234460369246853 7026203466418961319233785)
            ·
              refine ⟨5269652599814220989425339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7026203466418961319233785 5269652599814220989425339)
              ·
                refine ⟨7904478899721331484138009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5269652599814220989425339 7904478899721331484138009)
                ·
                  refine ⟨5928359174790998613103507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7904478899721331484138009 5928359174790998613103507)
                  ·
                    refine ⟨8892538762186497919655261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5928359174790998613103507 8892538762186497919655261)
                    ·
                      refine ⟨3334702035819936719870723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8892538762186497919655261 3334702035819936719870723)
                      ·
                        rfl

theorem cell23_6494309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 2, 1, 2, 1, 3].length) (baseStart_6494309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494309 prefixEnd_6494309 := by exact prefixLift 6494309
  have htrace : WordTrace (prefixWord ++ tailWord_6494309) baseStart_6494309 baseEnd_6494309 := by
    simpa [prefixWord, tailWord_6494309, baseEnd_6494309] using wordTrace_append hprefix tailTrace_6494309
  have hstable : (prefixWord ++ tailWord_6494309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494309).length < 2 ^ (prefixWord ++ tailWord_6494309).sum := by decide
  have hdescent : baseEnd_6494309 < baseStart_6494309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494318 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5]
def baseStart_6494318 : Nat := 118140960795 + 6494318 * 2 ^ 59
def prefixEnd_6494318 : Nat := 4983230072969 + 3 ^ 40 * 6494318 * 2
def baseEnd_6494318 : Nat := 3334706657145827184658181

theorem tailTrace_6494318 : CollatzResearch.WordTrace tailWord_6494318 prefixEnd_6494318 3334706657145827184658181 := by
  unfold tailWord_6494318
  simp only [CollatzResearch.WordTrace]
  refine ⟨29608404610775312757033451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157911491257468334704178405 29608404610775312757033451)
  ·
    refine ⟨44412606916162969135550177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29608404610775312757033451 44412606916162969135550177)
    ·
      refine ⟨33309455187122226851662633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44412606916162969135550177 33309455187122226851662633)
      ·
        refine ⟨24982091390341670138746975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33309455187122226851662633 24982091390341670138746975)
        ·
          refine ⟨37473137085512505208120463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24982091390341670138746975 37473137085512505208120463)
          ·
            refine ⟨56209705628268757812180695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37473137085512505208120463 56209705628268757812180695)
            ·
              refine ⟨84314558442403136718271043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56209705628268757812180695 84314558442403136718271043)
              ·
                refine ⟨126471837663604705077406565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84314558442403136718271043 126471837663604705077406565)
                ·
                  refine ⟨23713469561925882202013731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126471837663604705077406565 23713469561925882202013731)
                  ·
                    refine ⟨35570204342888823303020597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23713469561925882202013731 35570204342888823303020597)
                    ·
                      refine ⟨3334706657145827184658181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35570204342888823303020597 3334706657145827184658181)
                      ·
                        rfl

theorem cell23_6494318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_6494318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494318 prefixEnd_6494318 := by exact prefixLift 6494318
  have htrace : WordTrace (prefixWord ++ tailWord_6494318) baseStart_6494318 baseEnd_6494318 := by
    simpa [prefixWord, tailWord_6494318, baseEnd_6494318] using wordTrace_append hprefix tailTrace_6494318
  have hstable : (prefixWord ++ tailWord_6494318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494318).length < 2 ^ (prefixWord ++ tailWord_6494318).sum := by decide
  have hdescent : baseEnd_6494318 < baseStart_6494318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494321 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 9]
def baseStart_6494321 : Nat := 118140960795 + 6494321 * 2 ^ 59
def prefixEnd_6494321 : Nat := 4983230072969 + 3 ^ 40 * 6494321 * 2
def baseEnd_6494321 : Nat := 370523133065310074768963

theorem tailTrace_6494321 : CollatzResearch.WordTrace tailWord_6494321 prefixEnd_6494321 370523133065310074768963 := by
  unfold tailWord_6494321
  simp only [CollatzResearch.WordTrace]
  refine ⟨236867346305191633568626817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157911564203461089045751211 236867346305191633568626817)
  ·
    refine ⟨177650509728893725176470113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236867346305191633568626817 177650509728893725176470113)
    ·
      refine ⟨133237882296670293882352585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177650509728893725176470113 133237882296670293882352585)
      ·
        refine ⟨99928411722502720411764439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133237882296670293882352585 99928411722502720411764439)
        ·
          refine ⟨149892617583754080617646659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99928411722502720411764439 149892617583754080617646659)
          ·
            refine ⟨224838926375631120926469989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149892617583754080617646659 224838926375631120926469989)
            ·
              refine ⟨42157298695430835173713123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 224838926375631120926469989 42157298695430835173713123)
              ·
                refine ⟨63235948043146252760569685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42157298695430835173713123 63235948043146252760569685)
                ·
                  refine ⟨370523133065310074768963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63235948043146252760569685 370523133065310074768963)
                  ·
                    rfl

theorem cell23_6494321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 9].length) (baseStart_6494321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494321 prefixEnd_6494321 := by exact prefixLift 6494321
  have htrace : WordTrace (prefixWord ++ tailWord_6494321) baseStart_6494321 baseEnd_6494321 := by
    simpa [prefixWord, tailWord_6494321, baseEnd_6494321] using wordTrace_append hprefix tailTrace_6494321
  have hstable : (prefixWord ++ tailWord_6494321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494321).length < 2 ^ (prefixWord ++ tailWord_6494321).sum := by decide
  have hdescent : baseEnd_6494321 < baseStart_6494321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494365 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_6494365 : Nat := 118140960795 + 6494365 * 2 ^ 59
def prefixEnd_6494365 : Nat := 4983230072969 + 3 ^ 40 * 6494365 * 2
def baseEnd_6494365 : Nat := 3334730790736588500770465

theorem tailTrace_6494365 : CollatzResearch.WordTrace tailWord_6494365 prefixEnd_6494365 3334730790736588500770465 := by
  unfold tailWord_6494365
  simp only [CollatzResearch.WordTrace]
  refine ⟨236868951117032229083228549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157912634078021486055485699 236868951117032229083228549)
  ·
    refine ⟨44412928334443542953105353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236868951117032229083228549 44412928334443542953105353)
    ·
      refine ⟨33309696250832657214829015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44412928334443542953105353 33309696250832657214829015)
      ·
        refine ⟨49964544376248985822243523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33309696250832657214829015 49964544376248985822243523)
        ·
          refine ⟨74946816564373478733365285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49964544376248985822243523 74946816564373478733365285)
          ·
            refine ⟨14052528105820027262505991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74946816564373478733365285 14052528105820027262505991)
            ·
              refine ⟨21078792158730040893758987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14052528105820027262505991 21078792158730040893758987)
              ·
                refine ⟨31618188238095061340638481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21078792158730040893758987 31618188238095061340638481)
                ·
                  refine ⟨23713641178571296005478861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31618188238095061340638481 23713641178571296005478861)
                  ·
                    refine ⟨8892615441964236002054573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23713641178571296005478861 8892615441964236002054573)
                    ·
                      refine ⟨3334730790736588500770465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8892615441964236002054573 3334730790736588500770465)
                      ·
                        rfl

theorem cell23_6494365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_6494365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494365 prefixEnd_6494365 := by exact prefixLift 6494365
  have htrace : WordTrace (prefixWord ++ tailWord_6494365) baseStart_6494365 baseEnd_6494365 := by
    simpa [prefixWord, tailWord_6494365, baseEnd_6494365] using wordTrace_append hprefix tailTrace_6494365
  have hstable : (prefixWord ++ tailWord_6494365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494365).length < 2 ^ (prefixWord ++ tailWord_6494365).sum := by decide
  have hdescent : baseEnd_6494365 < baseStart_6494365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494385 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 1, 7]
def baseStart_6494385 : Nat := 118140960795 + 6494385 * 2 ^ 59
def prefixEnd_6494385 : Nat := 4983230072969 + 3 ^ 40 * 6494385 * 2
def baseEnd_6494385 : Nat := 1111580353449892807506791

theorem tailTrace_6494385 : CollatzResearch.WordTrace tailWord_6494385 prefixEnd_6494385 1111580353449892807506791 := by
  unfold tailWord_6494385
  simp only [CollatzResearch.WordTrace]
  refine ⟨236869680576959772498956609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157913120384639848332637739 236869680576959772498956609)
  ·
    refine ⟨177652260432719829374217457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236869680576959772498956609 177652260432719829374217457)
    ·
      refine ⟨133239195324539872030663093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177652260432719829374217457 133239195324539872030663093)
      ·
        refine ⟨12491174561675613002874665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133239195324539872030663093 12491174561675613002874665)
        ·
          refine ⟨9368380921256709752155999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12491174561675613002874665 9368380921256709752155999)
          ·
            refine ⟨14052571381885064628233999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9368380921256709752155999 14052571381885064628233999)
            ·
              refine ⟨21078857072827596942350999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14052571381885064628233999 21078857072827596942350999)
              ·
                refine ⟨31618285609241395413526499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21078857072827596942350999 31618285609241395413526499)
                ·
                  refine ⟨47427428413862093120289749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31618285609241395413526499 47427428413862093120289749)
                  ·
                    refine ⟨1111580353449892807506791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47427428413862093120289749 1111580353449892807506791)
                    ·
                      rfl

theorem cell23_6494385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_6494385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494385 prefixEnd_6494385 := by exact prefixLift 6494385
  have htrace : WordTrace (prefixWord ++ tailWord_6494385) baseStart_6494385 baseEnd_6494385 := by
    simpa [prefixWord, tailWord_6494385, baseEnd_6494385] using wordTrace_append hprefix tailTrace_6494385
  have hstable : (prefixWord ++ tailWord_6494385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494385).length < 2 ^ (prefixWord ++ tailWord_6494385).sum := by decide
  have hdescent : baseEnd_6494385 < baseStart_6494385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494389 : List Nat := [1, 3, 3, 4, 1, 1, 2, 3, 5]
def baseStart_6494389 : Nat := 118140960795 + 6494389 * 2 ^ 59
def prefixEnd_6494389 : Nat := 4983230072969 + 3 ^ 40 * 6494389 * 2
def baseEnd_6494389 : Nat := 370527012696921822985595

theorem tailTrace_6494389 : CollatzResearch.WordTrace tailWord_6494389 prefixEnd_6494389 370527012696921822985595 := by
  unfold tailWord_6494389
  simp only [CollatzResearch.WordTrace]
  refine ⟨236869826468945281182102221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157913217645963520788068147 236869826468945281182102221)
  ·
    refine ⟨88826184925854480443288333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236869826468945281182102221 88826184925854480443288333)
    ·
      refine ⟨33309819347195430166233125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88826184925854480443288333 33309819347195430166233125)
      ·
        refine ⟨6245591127599143156168711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33309819347195430166233125 6245591127599143156168711)
        ·
          refine ⟨9368386691398714734253067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6245591127599143156168711 9368386691398714734253067)
          ·
            refine ⟨14052580037098072101379601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9368386691398714734253067 14052580037098072101379601)
            ·
              refine ⟨10539435027823554076034701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14052580037098072101379601 10539435027823554076034701)
              ·
                refine ⟨3952288135433832778513013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10539435027823554076034701 3952288135433832778513013)
                ·
                  refine ⟨370527012696921822985595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3952288135433832778513013 370527012696921822985595)
                  ·
                    rfl

theorem cell23_6494389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 2, 3, 5].length) (baseStart_6494389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494389 prefixEnd_6494389 := by exact prefixLift 6494389
  have htrace : WordTrace (prefixWord ++ tailWord_6494389) baseStart_6494389 baseEnd_6494389 := by
    simpa [prefixWord, tailWord_6494389, baseEnd_6494389] using wordTrace_append hprefix tailTrace_6494389
  have hstable : (prefixWord ++ tailWord_6494389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494389).length < 2 ^ (prefixWord ++ tailWord_6494389).sum := by decide
  have hdescent : baseEnd_6494389 < baseStart_6494389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494405 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 2, 4, 2]
def baseStart_6494405 : Nat := 118140960795 + 6494405 * 2 ^ 59
def prefixEnd_6494405 : Nat := 4983230072969 + 3 ^ 40 * 6494405 * 2
def baseEnd_6494405 : Nat := 3334751329962768344270281

theorem tailTrace_6494405 : CollatzResearch.WordTrace tailWord_6494405 prefixEnd_6494405 3334751329962768344270281 := by
  unfold tailWord_6494405
  simp only [CollatzResearch.WordTrace]
  refine ⟨236870410036887315914684669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157913606691258210609789779 236870410036887315914684669)
  ·
    refine ⟨88826403763832743468006751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236870410036887315914684669 88826403763832743468006751)
    ·
      refine ⟨133239605645749115202010127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88826403763832743468006751 133239605645749115202010127)
      ·
        refine ⟨199859408468623672803015191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133239605645749115202010127 199859408468623672803015191)
        ·
          refine ⟨299789112702935509204522787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199859408468623672803015191 299789112702935509204522787)
          ·
            refine ⟨449683669054403263806784181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299789112702935509204522787 449683669054403263806784181)
            ·
              refine ⟨42157843973850305981886017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 449683669054403263806784181 42157843973850305981886017)
              ·
                refine ⟨31618382980387729486414513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42157843973850305981886017 31618382980387729486414513)
                ·
                  refine ⟨23713787235290797114810885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31618382980387729486414513 23713787235290797114810885)
                  ·
                    refine ⟨4446335106617024459027041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23713787235290797114810885 4446335106617024459027041)
                    ·
                      refine ⟨3334751329962768344270281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446335106617024459027041 3334751329962768344270281)
                      ·
                        rfl

theorem cell23_6494405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 4, 2].length) (baseStart_6494405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494405 prefixEnd_6494405 := by exact prefixLift 6494405
  have htrace : WordTrace (prefixWord ++ tailWord_6494405) baseStart_6494405 baseEnd_6494405 := by
    simpa [prefixWord, tailWord_6494405, baseEnd_6494405] using wordTrace_append hprefix tailTrace_6494405
  have hstable : (prefixWord ++ tailWord_6494405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494405).length < 2 ^ (prefixWord ++ tailWord_6494405).sum := by decide
  have hdescent : baseEnd_6494405 < baseStart_6494405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494415 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 3, 4]
def baseStart_6494415 : Nat := 118140960795 + 6494415 * 2 ^ 59
def prefixEnd_6494415 : Nat := 4983230072969 + 3 ^ 40 * 6494415 * 2
def baseEnd_6494415 : Nat := 1111585488256437768381745

theorem tailTrace_6494415 : CollatzResearch.WordTrace tailWord_6494415 prefixEnd_6494415 1111585488256437768381745 := by
  unfold tailWord_6494415
  simp only [CollatzResearch.WordTrace]
  refine ⟨236870774766851087622548699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157913849844567391748365799 236870774766851087622548699)
  ·
    refine ⟨355306162150276631433823049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236870774766851087622548699 355306162150276631433823049)
    ·
      refine ⟨266479621612707473575367287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355306162150276631433823049 266479621612707473575367287)
      ·
        refine ⟨399719432419061210363050931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266479621612707473575367287 399719432419061210363050931)
        ·
          refine ⟨599579148628591815544576397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399719432419061210363050931 599579148628591815544576397)
          ·
            refine ⟨224842180735721930829216149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 599579148628591815544576397 224842180735721930829216149)
            ·
              refine ⟨10539477221986965507619507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 224842180735721930829216149 10539477221986965507619507)
              ·
                refine ⟨15809215832980448261429261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10539477221986965507619507 15809215832980448261429261)
                ·
                  refine ⟨5928455937367668098035973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15809215832980448261429261 5928455937367668098035973)
                  ·
                    refine ⟨1111585488256437768381745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5928455937367668098035973 1111585488256437768381745)
                    ·
                      rfl

theorem cell23_6494415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 4].length) (baseStart_6494415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494415 prefixEnd_6494415 := by exact prefixLift 6494415
  have htrace : WordTrace (prefixWord ++ tailWord_6494415) baseStart_6494415 baseEnd_6494415 := by
    simpa [prefixWord, tailWord_6494415, baseEnd_6494415] using wordTrace_append hprefix tailTrace_6494415
  have hstable : (prefixWord ++ tailWord_6494415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494415).length < 2 ^ (prefixWord ++ tailWord_6494415).sum := by decide
  have hdescent : baseEnd_6494415 < baseStart_6494415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494422 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_6494422 : Nat := 118140960795 + 6494422 * 2 ^ 59
def prefixEnd_6494422 : Nat := 4983230072969 + 3 ^ 40 * 6494422 * 2
def baseEnd_6494422 : Nat := 3334760059133894777757703

theorem tailTrace_6494422 : CollatzResearch.WordTrace tailWord_6494422 prefixEnd_6494422 3334760059133894777757703 := by
  unfold tailWord_6494422
  simp only [CollatzResearch.WordTrace]
  refine ⟨14804439379864107988628345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 157914020051883818545369013 14804439379864107988628345)
  ·
    refine ⟨11103329534898080991471259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14804439379864107988628345 11103329534898080991471259)
    ·
      refine ⟨16654994302347121487206889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11103329534898080991471259 16654994302347121487206889)
      ·
        refine ⟨12491245726760341115405167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16654994302347121487206889 12491245726760341115405167)
        ·
          refine ⟨18736868590140511673107751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12491245726760341115405167 18736868590140511673107751)
          ·
            refine ⟨28105302885210767509661627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18736868590140511673107751 28105302885210767509661627)
            ·
              refine ⟨42157954327816151264492441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28105302885210767509661627 42157954327816151264492441)
              ·
                refine ⟨31618465745862113448369331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42157954327816151264492441 31618465745862113448369331)
                ·
                  refine ⟨47427698618793170172553997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31618465745862113448369331 47427698618793170172553997)
                  ·
                    refine ⟨17785386982047438814707749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47427698618793170172553997 17785386982047438814707749)
                    ·
                      refine ⟨3334760059133894777757703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17785386982047438814707749 3334760059133894777757703)
                      ·
                        rfl

theorem cell23_6494422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_6494422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494422 prefixEnd_6494422 := by exact prefixLift 6494422
  have htrace : WordTrace (prefixWord ++ tailWord_6494422) baseStart_6494422 baseEnd_6494422 := by
    simpa [prefixWord, tailWord_6494422, baseEnd_6494422] using wordTrace_append hprefix tailTrace_6494422
  have hstable : (prefixWord ++ tailWord_6494422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494422).length < 2 ^ (prefixWord ++ tailWord_6494422).sum := by decide
  have hdescent : baseEnd_6494422 < baseStart_6494422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494512 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 7, 2, 2]
def baseStart_6494512 : Nat := 118140960795 + 6494512 * 2 ^ 59
def prefixEnd_6494512 : Nat := 4983230072969 + 3 ^ 40 * 6494512 * 2
def baseEnd_6494512 : Nat := 3334806272392799425632289

theorem tailTrace_6494512 : CollatzResearch.WordTrace tailWord_6494512 prefixEnd_6494512 3334806272392799425632289 := by
  unfold tailWord_6494512
  simp only [CollatzResearch.WordTrace]
  refine ⟨118437156323749836594414895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157916208431666448792553193 118437156323749836594414895)
  ·
    refine ⟨177655734485624754891622343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118437156323749836594414895 177655734485624754891622343)
    ·
      refine ⟨266483601728437132337433515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177655734485624754891622343 266483601728437132337433515)
      ·
        refine ⟨399725402592655698506150273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266483601728437132337433515 399725402592655698506150273)
        ·
          refine ⟨299794051944491773879612705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399725402592655698506150273 299794051944491773879612705)
          ·
            refine ⟨224845538958368830409709529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 299794051944491773879612705 224845538958368830409709529)
            ·
              refine ⟨168634154218776622807282147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224845538958368830409709529 168634154218776622807282147)
              ·
                refine ⟨252951231328164934210923221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168634154218776622807282147 252951231328164934210923221)
                ·
                  refine ⟨5928544484253865645568513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 252951231328164934210923221 5928544484253865645568513)
                  ·
                    refine ⟨4446408363190399234176385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5928544484253865645568513 4446408363190399234176385)
                    ·
                      refine ⟨3334806272392799425632289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446408363190399234176385 3334806272392799425632289)
                      ·
                        rfl

theorem cell23_6494512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 7, 2, 2].length) (baseStart_6494512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494512 prefixEnd_6494512 := by exact prefixLift 6494512
  have htrace : WordTrace (prefixWord ++ tailWord_6494512) baseStart_6494512 baseEnd_6494512 := by
    simpa [prefixWord, tailWord_6494512, baseEnd_6494512] using wordTrace_append hprefix tailTrace_6494512
  have hstable : (prefixWord ++ tailWord_6494512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494512).length < 2 ^ (prefixWord ++ tailWord_6494512).sum := by decide
  have hdescent : baseEnd_6494512 < baseStart_6494512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494522 : List Nat := [3, 1, 1, 1, 4, 2, 1, 4, 2, 4]
def baseStart_6494522 : Nat := 118140960795 + 6494522 * 2 ^ 59
def prefixEnd_6494522 : Nat := 4983230072969 + 3 ^ 40 * 6494522 * 2
def baseEnd_6494522 : Nat := 1111603802399781462169081

theorem tailTrace_6494522 : CollatzResearch.WordTrace tailWord_6494522 prefixEnd_6494522 1111603802399781462169081 := by
  unfold tailWord_6494522
  simp only [CollatzResearch.WordTrace]
  refine ⟨59218669344365861224173455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157916451584975629931129213 59218669344365861224173455)
  ·
    refine ⟨88828004016548791836260183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59218669344365861224173455 88828004016548791836260183)
    ·
      refine ⟨133242006024823187754390275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88828004016548791836260183 133242006024823187754390275)
      ·
        refine ⟨199863009037234781631585413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133242006024823187754390275 199863009037234781631585413)
        ·
          refine ⟨37474314194481521555922265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199863009037234781631585413 37474314194481521555922265)
          ·
            refine ⟨28105735645861141166941699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37474314194481521555922265 28105735645861141166941699)
            ·
              refine ⟨42158603468791711750412549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28105735645861141166941699 42158603468791711750412549)
              ·
                refine ⟨7904738150398445953202353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42158603468791711750412549 7904738150398445953202353)
                ·
                  refine ⟨5928553612798834464901765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7904738150398445953202353 5928553612798834464901765)
                  ·
                    refine ⟨1111603802399781462169081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5928553612798834464901765 1111603802399781462169081)
                    ·
                      rfl

theorem cell23_6494522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 2, 4].length) (baseStart_6494522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494522 prefixEnd_6494522 := by exact prefixLift 6494522
  have htrace : WordTrace (prefixWord ++ tailWord_6494522) baseStart_6494522 baseEnd_6494522 := by
    simpa [prefixWord, tailWord_6494522, baseEnd_6494522] using wordTrace_append hprefix tailTrace_6494522
  have hstable : (prefixWord ++ tailWord_6494522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494522).length < 2 ^ (prefixWord ++ tailWord_6494522).sum := by decide
  have hdescent : baseEnd_6494522 < baseStart_6494522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494528 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 7]
def baseStart_6494528 : Nat := 118140960795 + 6494528 * 2 ^ 59
def prefixEnd_6494528 : Nat := 4983230072969 + 3 ^ 40 * 6494528 * 2
def baseEnd_6494528 : Nat := 3334814488083271363032215

theorem tailTrace_6494528 : CollatzResearch.WordTrace tailWord_6494528 prefixEnd_6494528 3334814488083271363032215 := by
  unfold tailWord_6494528
  simp only [CollatzResearch.WordTrace]
  refine ⟨118437448107720853960706119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157916597476961138614274825 118437448107720853960706119)
  ·
    refine ⟨177656172161581280941059179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118437448107720853960706119 177656172161581280941059179)
    ·
      refine ⟨266484258242371921411588769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 177656172161581280941059179 266484258242371921411588769)
      ·
        refine ⟨199863193681778941058691577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 266484258242371921411588769 199863193681778941058691577)
        ·
          refine ⟨149897395261334205794018683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199863193681778941058691577 149897395261334205794018683)
          ·
            refine ⟨224846092892001308691028025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149897395261334205794018683 224846092892001308691028025)
            ·
              refine ⟨168634569669000981518271019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224846092892001308691028025 168634569669000981518271019)
              ·
                refine ⟨252951854503501472277406529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168634569669000981518271019 252951854503501472277406529)
                ·
                  refine ⟨189713890877626104208054897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252951854503501472277406529 189713890877626104208054897)
                  ·
                    refine ⟨142285418158219578156041173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 189713890877626104208054897 142285418158219578156041173)
                    ·
                      refine ⟨3334814488083271363032215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142285418158219578156041173 3334814488083271363032215)
                      ·
                        rfl

theorem cell23_6494528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_6494528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494528 prefixEnd_6494528 := by exact prefixLift 6494528
  have htrace : WordTrace (prefixWord ++ tailWord_6494528) baseStart_6494528 baseEnd_6494528 := by
    simpa [prefixWord, tailWord_6494528, baseEnd_6494528] using wordTrace_append hprefix tailTrace_6494528
  have hstable : (prefixWord ++ tailWord_6494528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494528).length < 2 ^ (prefixWord ++ tailWord_6494528).sum := by decide
  have hdescent : baseEnd_6494528 < baseStart_6494528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494596 : List Nat := [2, 3, 2, 1, 1, 2, 5, 1, 2, 1, 3]
def baseStart_6494596 : Nat := 118140960795 + 6494596 * 2 ^ 59
def prefixEnd_6494596 : Nat := 4983230072969 + 3 ^ 40 * 6494596 * 2
def baseEnd_6494596 : Nat := 3334849404767777096981903

theorem tailTrace_6494596 : CollatzResearch.WordTrace tailWord_6494596 prefixEnd_6494596 3334849404767777096981903 := by
  unfold tailWord_6494596
  simp only [CollatzResearch.WordTrace]
  refine ⟨118438688189597677767443821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157918250919463570356591761 118438688189597677767443821)
  ·
    refine ⟨44414508071099129162791433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118438688189597677767443821 44414508071099129162791433)
    ·
      refine ⟨33310881053324346872093575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44414508071099129162791433 33310881053324346872093575)
      ·
        refine ⟨49966321579986520308140363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33310881053324346872093575 49966321579986520308140363)
        ·
          refine ⟨74949482369979780462210545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49966321579986520308140363 74949482369979780462210545)
          ·
            refine ⟨56212111777484835346657909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74949482369979780462210545 56212111777484835346657909)
            ·
              refine ⟨5269885479139203313749179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56212111777484835346657909 5269885479139203313749179)
              ·
                refine ⟨7904828218708804970623769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5269885479139203313749179 7904828218708804970623769)
                ·
                  refine ⟨5928621164031603727967827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7904828218708804970623769 5928621164031603727967827)
                  ·
                    refine ⟨8892931746047405591951741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5928621164031603727967827 8892931746047405591951741)
                    ·
                      refine ⟨3334849404767777096981903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8892931746047405591951741 3334849404767777096981903)
                      ·
                        rfl

theorem cell23_6494596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 5, 1, 2, 1, 3].length) (baseStart_6494596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494596 prefixEnd_6494596 := by exact prefixLift 6494596
  have htrace : WordTrace (prefixWord ++ tailWord_6494596) baseStart_6494596 baseEnd_6494596 := by
    simpa [prefixWord, tailWord_6494596, baseEnd_6494596] using wordTrace_append hprefix tailTrace_6494596
  have hstable : (prefixWord ++ tailWord_6494596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494596).length < 2 ^ (prefixWord ++ tailWord_6494596).sum := by decide
  have hdescent : baseEnd_6494596 < baseStart_6494596 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494606 : List Nat := [4, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2]
def baseStart_6494606 : Nat := 118140960795 + 6494606 * 2 ^ 59
def prefixEnd_6494606 : Nat := 4983230072969 + 3 ^ 40 * 6494606 * 2
def baseEnd_6494606 : Nat := 3334854539574322057856857

theorem tailTrace_6494606 : CollatzResearch.WordTrace tailWord_6494606 prefixEnd_6494606 3334854539574322057856857 := by
  unfold tailWord_6494606
  simp only [CollatzResearch.WordTrace]
  refine ⟨29609717638644890905343959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 157918494072772751495167781 29609717638644890905343959)
  ·
    refine ⟨44414576457967336358015939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29609717638644890905343959 44414576457967336358015939)
    ·
      refine ⟨66621864686951004537023909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44414576457967336358015939 66621864686951004537023909)
      ·
        refine ⟨12491599628803313350691983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66621864686951004537023909 12491599628803313350691983)
        ·
          refine ⟨18737399443204970026037975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12491599628803313350691983 18737399443204970026037975)
          ·
            refine ⟨28106099164807455039056963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18737399443204970026037975 28106099164807455039056963)
            ·
              refine ⟨42159148747211182558585445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28106099164807455039056963 42159148747211182558585445)
              ·
                refine ⟨7904840390102096729734771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42159148747211182558585445 7904840390102096729734771)
                ·
                  refine ⟨11857260585153145094602157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7904840390102096729734771 11857260585153145094602157)
                  ·
                    refine ⟨4446472719432429410475809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11857260585153145094602157 4446472719432429410475809)
                    ·
                      refine ⟨3334854539574322057856857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446472719432429410475809 3334854539574322057856857)
                      ·
                        rfl

theorem cell23_6494606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_6494606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494606 prefixEnd_6494606 := by exact prefixLift 6494606
  have htrace : WordTrace (prefixWord ++ tailWord_6494606) baseStart_6494606 baseEnd_6494606 := by
    simpa [prefixWord, tailWord_6494606, baseEnd_6494606] using wordTrace_append hprefix tailTrace_6494606
  have hstable : (prefixWord ++ tailWord_6494606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494606).length < 2 ^ (prefixWord ++ tailWord_6494606).sum := by decide
  have hdescent : baseEnd_6494606 < baseStart_6494606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494615 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 4]
def baseStart_6494615 : Nat := 118140960795 + 6494615 * 2 ^ 59
def prefixEnd_6494615 : Nat := 4983230072969 + 3 ^ 40 * 6494615 * 2
def baseEnd_6494615 : Nat := 3334859160900212522644315

theorem tailTrace_6494615 : CollatzResearch.WordTrace tailWord_6494615 prefixEnd_6494615 3334859160900212522644315 := by
  unfold tailWord_6494615
  simp only [CollatzResearch.WordTrace]
  refine ⟨236878069366126521779829299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157918712910751014519886199 236878069366126521779829299)
  ·
    refine ⟨355317104049189782669743949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236878069366126521779829299 355317104049189782669743949)
    ·
      refine ⟨133243914018446168501153981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 355317104049189782669743949 133243914018446168501153981)
      ·
        refine ⟨49966467756917313187932743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133243914018446168501153981 49966467756917313187932743)
        ·
          refine ⟨74949701635375969781899115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49966467756917313187932743 74949701635375969781899115)
          ·
            refine ⟨112424552453063954672848673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74949701635375969781899115 112424552453063954672848673)
            ·
              refine ⟨84318414339797966004636505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112424552453063954672848673 84318414339797966004636505)
              ·
                refine ⟨63238810754848474503477379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84318414339797966004636505 63238810754848474503477379)
                ·
                  refine ⟨94858216132272711755216069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63238810754848474503477379 94858216132272711755216069)
                  ·
                    refine ⟨17785915524801133454103013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94858216132272711755216069 17785915524801133454103013)
                    ·
                      refine ⟨3334859160900212522644315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17785915524801133454103013 3334859160900212522644315)
                      ·
                        rfl

theorem cell23_6494615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_6494615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494615 prefixEnd_6494615 := by exact prefixLift 6494615
  have htrace : WordTrace (prefixWord ++ tailWord_6494615) baseStart_6494615 baseEnd_6494615 := by
    simpa [prefixWord, tailWord_6494615, baseEnd_6494615] using wordTrace_append hprefix tailTrace_6494615
  have hstable : (prefixWord ++ tailWord_6494615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494615).length < 2 ^ (prefixWord ++ tailWord_6494615).sum := by decide
  have hdescent : baseEnd_6494615 < baseStart_6494615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494653 : List Nat := [1, 4, 1, 2, 2, 2, 4, 1, 2, 2, 2]
def baseStart_6494653 : Nat := 118140960795 + 6494653 * 2 ^ 59
def prefixEnd_6494653 : Nat := 4983230072969 + 3 ^ 40 * 6494653 * 2
def baseEnd_6494653 : Nat := 3334878673165083373969141

theorem tailTrace_6494653 : CollatzResearch.WordTrace tailWord_6494653 prefixEnd_6494653 3334878673165083373969141 := by
  unfold tailWord_6494653
  simp only [CollatzResearch.WordTrace]
  refine ⟨236879455339988854269712613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157919636893325902846475075 236879455339988854269712613)
  ·
    refine ⟨44414897876247910175571115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236879455339988854269712613 44414897876247910175571115)
    ·
      refine ⟨66622346814371865263356673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44414897876247910175571115 66622346814371865263356673)
      ·
        refine ⟨49966760110778898947517505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66622346814371865263356673 49966760110778898947517505)
        ·
          refine ⟨37475070083084174210638129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49966760110778898947517505 37475070083084174210638129)
          ·
            refine ⟨28106302562313130657978597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37475070083084174210638129 28106302562313130657978597)
            ·
              refine ⟨5269931730433711998370987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28106302562313130657978597 5269931730433711998370987)
              ·
                refine ⟨7904897595650567997556481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5269931730433711998370987 7904897595650567997556481)
                ·
                  refine ⟨5928673196737925998167361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7904897595650567997556481 5928673196737925998167361)
                  ·
                    refine ⟨4446504897553444498625521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5928673196737925998167361 4446504897553444498625521)
                    ·
                      refine ⟨3334878673165083373969141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446504897553444498625521 3334878673165083373969141)
                      ·
                        rfl

theorem cell23_6494653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_6494653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494653 prefixEnd_6494653 := by exact prefixLift 6494653
  have htrace : WordTrace (prefixWord ++ tailWord_6494653) baseStart_6494653 baseEnd_6494653 := by
    simpa [prefixWord, tailWord_6494653, baseEnd_6494653] using wordTrace_append hprefix tailTrace_6494653
  have hstable : (prefixWord ++ tailWord_6494653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494653).length < 2 ^ (prefixWord ++ tailWord_6494653).sum := by decide
  have hdescent : baseEnd_6494653 < baseStart_6494653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494657 : List Nat := [1, 2, 7, 1, 1, 2, 1, 2, 1, 3, 2]
def baseStart_6494657 : Nat := 118140960795 + 6494657 * 2 ^ 59
def prefixEnd_6494657 : Nat := 4983230072969 + 3 ^ 40 * 6494657 * 2
def baseEnd_6494657 : Nat := 3334880727087701358319123

theorem tailTrace_6494657 : CollatzResearch.WordTrace tailWord_6494657 prefixEnd_6494657 3334880727087701358319123 := by
  unfold tailWord_6494657
  simp only [CollatzResearch.WordTrace]
  refine ⟨236879601231974362952858225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157919734154649575301905483 236879601231974362952858225)
  ·
    refine ⟨177659700923980772214643669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236879601231974362952858225 177659700923980772214643669)
    ·
      refine ⟨4163899240405799348780711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 177659700923980772214643669 4163899240405799348780711)
      ·
        refine ⟨6245848860608699023171067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4163899240405799348780711 6245848860608699023171067)
        ·
          refine ⟨9368773290913048534756601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6245848860608699023171067 9368773290913048534756601)
          ·
            refine ⟨7026579968184786401067451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9368773290913048534756601 7026579968184786401067451)
            ·
              refine ⟨10539869952277179601601177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7026579968184786401067451 10539869952277179601601177)
              ·
                refine ⟨7904902464207884701200883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10539869952277179601601177 7904902464207884701200883)
                ·
                  refine ⟨11857353696311827051801325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7904902464207884701200883 11857353696311827051801325)
                  ·
                    refine ⟨4446507636116935144425497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11857353696311827051801325 4446507636116935144425497)
                    ·
                      refine ⟨3334880727087701358319123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446507636116935144425497 3334880727087701358319123)
                      ·
                        rfl

theorem cell23_6494657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_6494657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494657 prefixEnd_6494657 := by exact prefixLift 6494657
  have htrace : WordTrace (prefixWord ++ tailWord_6494657) baseStart_6494657 baseEnd_6494657 := by
    simpa [prefixWord, tailWord_6494657, baseEnd_6494657] using wordTrace_append hprefix tailTrace_6494657
  have hstable : (prefixWord ++ tailWord_6494657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494657).length < 2 ^ (prefixWord ++ tailWord_6494657).sum := by decide
  have hdescent : baseEnd_6494657 < baseStart_6494657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494675 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 4]
def baseStart_6494675 : Nat := 118140960795 + 6494675 * 2 ^ 59
def prefixEnd_6494675 : Nat := 4983230072969 + 3 ^ 40 * 6494675 * 2
def baseEnd_6494675 : Nat := 3334889969739482287894039

theorem tailTrace_6494675 : CollatzResearch.WordTrace tailWord_6494675 prefixEnd_6494675 3334889969739482287894039 := by
  unfold tailWord_6494675
  simp only [CollatzResearch.WordTrace]
  refine ⟨236880257745909152027013479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157920171830606101351342319 236880257745909152027013479)
  ·
    refine ⟨355320386618863728040520219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236880257745909152027013479 355320386618863728040520219)
    ·
      refine ⟨532980579928295592060780329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355320386618863728040520219 532980579928295592060780329)
      ·
        refine ⟨399735434946221694045585247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532980579928295592060780329 399735434946221694045585247)
        ·
          refine ⟨599603152419332541068377871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399735434946221694045585247 599603152419332541068377871)
          ·
            refine ⟨899404728628998811602566807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599603152419332541068377871 899404728628998811602566807)
            ·
              refine ⟨1349107092943498217403850211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899404728628998811602566807 1349107092943498217403850211)
              ·
                refine ⟨2023660639415247326105775317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349107092943498217403850211 2023660639415247326105775317)
                ·
                  refine ⟨47429546236294859205604109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2023660639415247326105775317 47429546236294859205604109)
                  ·
                    refine ⟨17786079838610572202101541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47429546236294859205604109 17786079838610572202101541)
                    ·
                      refine ⟨3334889969739482287894039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17786079838610572202101541 3334889969739482287894039)
                      ·
                        rfl

theorem cell23_6494675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_6494675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494675 prefixEnd_6494675 := by exact prefixLift 6494675
  have htrace : WordTrace (prefixWord ++ tailWord_6494675) baseStart_6494675 baseEnd_6494675 := by
    simpa [prefixWord, tailWord_6494675, baseEnd_6494675] using wordTrace_append hprefix tailTrace_6494675
  have hstable : (prefixWord ++ tailWord_6494675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494675).length < 2 ^ (prefixWord ++ tailWord_6494675).sum := by decide
  have hdescent : baseEnd_6494675 < baseStart_6494675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494693 : List Nat := [1, 3, 1, 5, 2, 2, 2, 2, 5]
def baseStart_6494693 : Nat := 118140960795 + 6494693 * 2 ^ 59
def prefixEnd_6494693 : Nat := 4983230072969 + 3 ^ 40 * 6494693 * 2
def baseEnd_6494693 : Nat := 370544356932362579718773

theorem tailTrace_6494693 : CollatzResearch.WordTrace tailWord_6494693 prefixEnd_6494693 370544356932362579718773 := by
  unfold tailWord_6494693
  simp only [CollatzResearch.WordTrace]
  refine ⟨236880914259843941101168733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157920609506562627400779155 236880914259843941101168733)
  ·
    refine ⟨88830342847441477912938275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236880914259843941101168733 88830342847441477912938275)
    ·
      refine ⟨133245514271162216869407413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88830342847441477912938275 133245514271162216869407413)
      ·
        refine ⟨12491766962921457831506945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 133245514271162216869407413 12491766962921457831506945)
        ·
          refine ⟨9368825222191093373630209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12491766962921457831506945 9368825222191093373630209)
          ·
            refine ⟨7026618916643320030222657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9368825222191093373630209 7026618916643320030222657)
            ·
              refine ⟨5269964187482490022666993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7026618916643320030222657 5269964187482490022666993)
              ·
                refine ⟨3952473140611867517000245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5269964187482490022666993 3952473140611867517000245)
                ·
                  refine ⟨370544356932362579718773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3952473140611867517000245 370544356932362579718773)
                  ·
                    rfl

theorem cell23_6494693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 5].length) (baseStart_6494693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494693 prefixEnd_6494693 := by exact prefixLift 6494693
  have htrace : WordTrace (prefixWord ++ tailWord_6494693) baseStart_6494693 baseEnd_6494693 := by
    simpa [prefixWord, tailWord_6494693, baseEnd_6494693] using wordTrace_append hprefix tailTrace_6494693
  have hstable : (prefixWord ++ tailWord_6494693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494693).length < 2 ^ (prefixWord ++ tailWord_6494693).sum := by decide
  have hdescent : baseEnd_6494693 < baseStart_6494693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494712 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 1, 4, 3]
def baseStart_6494712 : Nat := 118140960795 + 6494712 * 2 ^ 59
def prefixEnd_6494712 : Nat := 4983230072969 + 3 ^ 40 * 6494712 * 2
def baseEnd_6494712 : Nat := 3334908968523698643131369

theorem tailTrace_6494712 : CollatzResearch.WordTrace tailWord_6494712 prefixEnd_6494712 3334908968523698643131369 := by
  unfold tailWord_6494712
  simp only [CollatzResearch.WordTrace]
  refine ⟨118440803623387553673055195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157921071497850071564073593 118440803623387553673055195)
  ·
    refine ⟨177661205435081330509582793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118440803623387553673055195 177661205435081330509582793)
    ·
      refine ⟨133245904076310997882187095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177661205435081330509582793 133245904076310997882187095)
      ·
        refine ⟨199868856114466496823280643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133245904076310997882187095 199868856114466496823280643)
        ·
          refine ⟨299803284171699745234920965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199868856114466496823280643 299803284171699745234920965)
          ·
            refine ⟨56213115782193702231547681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 299803284171699745234920965 56213115782193702231547681)
            ·
              refine ⟨42159836836645276673660761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56213115782193702231547681 42159836836645276673660761)
              ·
                refine ⟨31619877627483957505245571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42159836836645276673660761 31619877627483957505245571)
                ·
                  refine ⟨47429816441225936257868357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31619877627483957505245571 47429816441225936257868357)
                  ·
                    refine ⟨8893090582729863048350317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47429816441225936257868357 8893090582729863048350317)
                    ·
                      refine ⟨3334908968523698643131369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8893090582729863048350317 3334908968523698643131369)
                      ·
                        rfl

theorem cell23_6494712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 1, 4, 3].length) (baseStart_6494712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494712 prefixEnd_6494712 := by exact prefixLift 6494712
  have htrace : WordTrace (prefixWord ++ tailWord_6494712) baseStart_6494712 baseEnd_6494712 := by
    simpa [prefixWord, tailWord_6494712, baseEnd_6494712] using wordTrace_append hprefix tailTrace_6494712
  have hstable : (prefixWord ++ tailWord_6494712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494712).length < 2 ^ (prefixWord ++ tailWord_6494712).sum := by decide
  have hdescent : baseEnd_6494712 < baseStart_6494712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494735 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 8]
def baseStart_6494735 : Nat := 118140960795 + 6494735 * 2 ^ 59
def prefixEnd_6494735 : Nat := 4983230072969 + 3 ^ 40 * 6494735 * 2
def baseEnd_6494735 : Nat := 3334920778578752053143763

theorem tailTrace_6494735 : CollatzResearch.WordTrace tailWord_6494735 prefixEnd_6494735 3334920778578752053143763 := by
  unfold tailWord_6494735
  simp only [CollatzResearch.WordTrace]
  refine ⟨236882446125691782274197659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157921630750461188182798439 236882446125691782274197659)
  ·
    refine ⟨355323669188537673411296489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236882446125691782274197659 355323669188537673411296489)
    ·
      refine ⟨266492751891403255058472367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355323669188537673411296489 266492751891403255058472367)
      ·
        refine ⟨399739127837104882587708551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266492751891403255058472367 399739127837104882587708551)
        ·
          refine ⟨599608691755657323881562827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399739127837104882587708551 599608691755657323881562827)
          ·
            refine ⟨899413037633485985822344241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 599608691755657323881562827 899413037633485985822344241)
            ·
              refine ⟨674559778225114489366758181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899413037633485985822344241 674559778225114489366758181)
              ·
                refine ⟨126479958417208966756267159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 674559778225114489366758181 126479958417208966756267159)
                ·
                  refine ⟨189719937625813450134400739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126479958417208966756267159 189719937625813450134400739)
                  ·
                    refine ⟨284579906438720175201601109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 189719937625813450134400739 284579906438720175201601109)
                    ·
                      refine ⟨3334920778578752053143763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 284579906438720175201601109 3334920778578752053143763)
                      ·
                        rfl

theorem cell23_6494735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 8].length) (baseStart_6494735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494735 prefixEnd_6494735 := by exact prefixLift 6494735
  have htrace : WordTrace (prefixWord ++ tailWord_6494735) baseStart_6494735 baseEnd_6494735 := by
    simpa [prefixWord, tailWord_6494735, baseEnd_6494735] using wordTrace_append hprefix tailTrace_6494735
  have hstable : (prefixWord ++ tailWord_6494735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494735).length < 2 ^ (prefixWord ++ tailWord_6494735).sum := by decide
  have hdescent : baseEnd_6494735 < baseStart_6494735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494749 : List Nat := [1, 4, 2, 2, 1, 2, 3, 2, 6]
def baseStart_6494749 : Nat := 118140960795 + 6494749 * 2 ^ 59
def prefixEnd_6494749 : Nat := 4983230072969 + 3 ^ 40 * 6494749 * 2
def baseEnd_6494749 : Nat := 370547551923101666485411

theorem tailTrace_6494749 : CollatzResearch.WordTrace tailWord_6494749 prefixEnd_6494749 370547551923101666485411 := by
  unfold tailWord_6494749
  simp only [CollatzResearch.WordTrace]
  refine ⟨236882956747641062665207301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157921971165094041776804867 236882956747641062665207301)
  ·
    refine ⟨44415554390182699249726369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 236882956747641062665207301 44415554390182699249726369)
    ·
      refine ⟨33311665792637024437294777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44415554390182699249726369 33311665792637024437294777)
      ·
        refine ⟨24983749344477768327971083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33311665792637024437294777 24983749344477768327971083)
        ·
          refine ⟨37475624016716652491956625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24983749344477768327971083 37475624016716652491956625)
          ·
            refine ⟨28106718012537489368967469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37475624016716652491956625 28106718012537489368967469)
            ·
              refine ⟨10540019254701558513362801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28106718012537489368967469 10540019254701558513362801)
              ·
                refine ⟨7905014441026168885022101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10540019254701558513362801 7905014441026168885022101)
                ·
                  refine ⟨370547551923101666485411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7905014441026168885022101 370547551923101666485411)
                  ·
                    rfl

theorem cell23_6494749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 2, 6].length) (baseStart_6494749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494749 prefixEnd_6494749 := by exact prefixLift 6494749
  have htrace : WordTrace (prefixWord ++ tailWord_6494749) baseStart_6494749 baseEnd_6494749 := by
    simpa [prefixWord, tailWord_6494749, baseEnd_6494749] using wordTrace_append hprefix tailTrace_6494749
  have hstable : (prefixWord ++ tailWord_6494749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494749).length < 2 ^ (prefixWord ++ tailWord_6494749).sum := by decide
  have hdescent : baseEnd_6494749 < baseStart_6494749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494769 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 1, 5, 2]
def baseStart_6494769 : Nat := 118140960795 + 6494769 * 2 ^ 59
def prefixEnd_6494769 : Nat := 4983230072969 + 3 ^ 40 * 6494769 * 2
def baseEnd_6494769 : Nat := 3334938236921004920118607

theorem tailTrace_6494769 : CollatzResearch.WordTrace tailWord_6494769 prefixEnd_6494769 3334938236921004920118607 := by
  unfold tailWord_6494769
  simp only [CollatzResearch.WordTrace]
  refine ⟨236883686207568606080935361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157922457471712404053956907 236883686207568606080935361)
  ·
    refine ⟨177662764655676454560701521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 236883686207568606080935361 177662764655676454560701521)
    ·
      refine ⟨133247073491757340920526141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 177662764655676454560701521 133247073491757340920526141)
      ·
        refine ⟨49967652559409002845197303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133247073491757340920526141 49967652559409002845197303)
        ·
          refine ⟨74951478839113504267795955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49967652559409002845197303 74951478839113504267795955)
          ·
            refine ⟨112427218258670256401693933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74951478839113504267795955 112427218258670256401693933)
            ·
              refine ⟨42160206847001346150635225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112427218258670256401693933 42160206847001346150635225)
              ·
                refine ⟨31620155135251009612976419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42160206847001346150635225 31620155135251009612976419)
                ·
                  refine ⟨47430232702876514419464629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31620155135251009612976419 47430232702876514419464629)
                  ·
                    refine ⟨4446584315894673226824809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47430232702876514419464629 4446584315894673226824809)
                    ·
                      refine ⟨3334938236921004920118607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446584315894673226824809 3334938236921004920118607)
                      ·
                        rfl

theorem cell23_6494769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 5, 2].length) (baseStart_6494769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494769 prefixEnd_6494769 := by exact prefixLift 6494769
  have htrace : WordTrace (prefixWord ++ tailWord_6494769) baseStart_6494769 baseEnd_6494769 := by
    simpa [prefixWord, tailWord_6494769, baseEnd_6494769] using wordTrace_append hprefix tailTrace_6494769
  have hstable : (prefixWord ++ tailWord_6494769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494769).length < 2 ^ (prefixWord ++ tailWord_6494769).sum := by decide
  have hdescent : baseEnd_6494769 < baseStart_6494769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494792 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 1, 6]
def baseStart_6494792 : Nat := 118140960795 + 6494792 * 2 ^ 59
def prefixEnd_6494792 : Nat := 4983230072969 + 3 ^ 40 * 6494792 * 2
def baseEnd_6494792 : Nat := 1111650015658686110043667

theorem tailTrace_6494792 : CollatzResearch.WordTrace tailWord_6494792 prefixEnd_6494792 1111650015658686110043667 := by
  unfold tailWord_6494792
  simp only [CollatzResearch.WordTrace]
  refine ⟨118442262543242640504511315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 157923016724323520672681753 118442262543242640504511315)
  ·
    refine ⟨177663393814863960756766973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118442262543242640504511315 177663393814863960756766973)
    ·
      refine ⟨66623772680573985283787615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 177663393814863960756766973 66623772680573985283787615)
      ·
        refine ⟨99935659020860977925681423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66623772680573985283787615 99935659020860977925681423)
        ·
          refine ⟨149903488531291466888522135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99935659020860977925681423 149903488531291466888522135)
          ·
            refine ⟨224855232796937200332783203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149903488531291466888522135 224855232796937200332783203)
            ·
              refine ⟨337282849195405800499174805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224855232796937200332783203 337282849195405800499174805)
              ·
                refine ⟨15810133556034646898398819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 337282849195405800499174805 15810133556034646898398819)
                ·
                  refine ⟨23715200334051970347598229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15810133556034646898398819 23715200334051970347598229)
                  ·
                    refine ⟨1111650015658686110043667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23715200334051970347598229 1111650015658686110043667)
                    ·
                      rfl

theorem cell23_6494792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_6494792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494792 prefixEnd_6494792 := by exact prefixLift 6494792
  have htrace : WordTrace (prefixWord ++ tailWord_6494792) baseStart_6494792 baseEnd_6494792 := by
    simpa [prefixWord, tailWord_6494792, baseEnd_6494792] using wordTrace_append hprefix tailTrace_6494792
  have hstable : (prefixWord ++ tailWord_6494792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494792).length < 2 ^ (prefixWord ++ tailWord_6494792).sum := by decide
  have hdescent : baseEnd_6494792 < baseStart_6494792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494799 : List Nat := [1, 1, 2, 1, 1, 2, 6, 3, 1, 1, 4]
def baseStart_6494799 : Nat := 118140960795 + 6494799 * 2 ^ 59
def prefixEnd_6494799 : Nat := 4983230072969 + 3 ^ 40 * 6494799 * 2
def baseEnd_6494799 : Nat := 3334953641340639802743469

theorem tailTrace_6494799 : CollatzResearch.WordTrace tailWord_6494799 prefixEnd_6494799 3334953641340639802743469 := by
  unfold tailWord_6494799
  simp only [CollatzResearch.WordTrace]
  refine ⟨236884780397459921204527451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157923186931639947469684967 236884780397459921204527451)
  ·
    refine ⟨355327170596189881806791177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236884780397459921204527451 355327170596189881806791177)
    ·
      refine ⟨266495377947142411355093383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355327170596189881806791177 266495377947142411355093383)
      ·
        refine ⟨399743066920713617032640075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 266495377947142411355093383 399743066920713617032640075)
        ·
          refine ⟨599614600381070425548960113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399743066920713617032640075 599614600381070425548960113)
          ·
            refine ⟨449710950285802819161720085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599614600381070425548960113 449710950285802819161720085)
            ·
              refine ⟨21080200794647007148205629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 449710950285802819161720085 21080200794647007148205629)
              ·
                refine ⟨7905075297992627680577111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21080200794647007148205629 7905075297992627680577111)
                ·
                  refine ⟨11857612946988941520865667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7905075297992627680577111 11857612946988941520865667)
                  ·
                    refine ⟨17786419420483412281298501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11857612946988941520865667 17786419420483412281298501)
                    ·
                      refine ⟨3334953641340639802743469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17786419420483412281298501 3334953641340639802743469)
                      ·
                        rfl

theorem cell23_6494799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 1, 4].length) (baseStart_6494799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494799 prefixEnd_6494799 := by exact prefixLift 6494799
  have htrace : WordTrace (prefixWord ++ tailWord_6494799) baseStart_6494799 baseEnd_6494799 := by
    simpa [prefixWord, tailWord_6494799, baseEnd_6494799] using wordTrace_append hprefix tailTrace_6494799
  have hstable : (prefixWord ++ tailWord_6494799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494799).length < 2 ^ (prefixWord ++ tailWord_6494799).sum := by decide
  have hdescent : baseEnd_6494799 < baseStart_6494799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494819 : List Nat := [1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 3]
def baseStart_6494819 : Nat := 118140960795 + 6494819 * 2 ^ 59
def prefixEnd_6494819 : Nat := 4983230072969 + 3 ^ 40 * 6494819 * 2
def baseEnd_6494819 : Nat := 3334963910953729724493377

theorem tailTrace_6494819 : CollatzResearch.WordTrace tailWord_6494819 prefixEnd_6494819 3334963910953729724493377 := by
  unfold tailWord_6494819
  simp only [CollatzResearch.WordTrace]
  refine ⟨236885509857387464620255511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157923673238258309746837007 236885509857387464620255511)
  ·
    refine ⟨355328264786081196930383267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 236885509857387464620255511 355328264786081196930383267)
    ·
      refine ⟨532992397179121795395574901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355328264786081196930383267 532992397179121795395574901)
      ·
        refine ⟨49968037235542668318335147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 532992397179121795395574901 49968037235542668318335147)
        ·
          refine ⟨74952055853314002477502721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49968037235542668318335147 74952055853314002477502721)
          ·
            refine ⟨56214041889985501858127041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74952055853314002477502721 56214041889985501858127041)
            ·
              refine ⟨42160531417489126393595281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56214041889985501858127041 42160531417489126393595281)
              ·
                refine ⟨31620398563116844795196461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42160531417489126393595281 31620398563116844795196461)
                ·
                  refine ⟨11857649461168816798198673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31620398563116844795196461 11857649461168816798198673)
                  ·
                    refine ⟨8893237095876612598649005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11857649461168816798198673 8893237095876612598649005)
                    ·
                      refine ⟨3334963910953729724493377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8893237095876612598649005 3334963910953729724493377)
                      ·
                        rfl

theorem cell23_6494819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_6494819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494819 prefixEnd_6494819 := by exact prefixLift 6494819
  have htrace : WordTrace (prefixWord ++ tailWord_6494819) baseStart_6494819 baseEnd_6494819 := by
    simpa [prefixWord, tailWord_6494819, baseEnd_6494819] using wordTrace_append hprefix tailTrace_6494819
  have hstable : (prefixWord ++ tailWord_6494819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494819).length < 2 ^ (prefixWord ++ tailWord_6494819).sum := by decide
  have hdescent : baseEnd_6494819 < baseStart_6494819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494826 : List Nat := [3, 1, 3, 2, 1, 1, 3, 3, 2, 4]
def baseStart_6494826 : Nat := 118140960795 + 6494826 * 2 ^ 59
def prefixEnd_6494826 : Nat := 4983230072969 + 3 ^ 40 * 6494826 * 2
def baseEnd_6494826 : Nat := 1111655835106103732368615

theorem tailTrace_6494826 : CollatzResearch.WordTrace tailWord_6494826 prefixEnd_6494826 1111655835106103732368615 := by
  unfold tailWord_6494826
  simp only [CollatzResearch.WordTrace]
  refine ⟨59221441292090526203940083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157923843445574736543840221 59221441292090526203940083)
  ·
    refine ⟨88832161938135789305910125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59221441292090526203940083 88832161938135789305910125)
    ·
      refine ⟨33312060726800920989716297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 88832161938135789305910125 33312060726800920989716297)
      ·
        refine ⟨24984045545100690742287223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33312060726800920989716297 24984045545100690742287223)
        ·
          refine ⟨37476068317651036113430835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24984045545100690742287223 37476068317651036113430835)
          ·
            refine ⟨56214102476476554170146253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37476068317651036113430835 56214102476476554170146253)
            ·
              refine ⟨21080288428678707813804845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56214102476476554170146253 21080288428678707813804845)
              ·
                refine ⟨7905108160754515430176817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21080288428678707813804845 7905108160754515430176817)
                ·
                  refine ⟨5928831120565886572632613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7905108160754515430176817 5928831120565886572632613)
                  ·
                    refine ⟨1111655835106103732368615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5928831120565886572632613 1111655835106103732368615)
                    ·
                      rfl

theorem cell23_6494826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 2, 4].length) (baseStart_6494826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494826 prefixEnd_6494826 := by exact prefixLift 6494826
  have htrace : WordTrace (prefixWord ++ tailWord_6494826) baseStart_6494826 baseEnd_6494826 := by
    simpa [prefixWord, tailWord_6494826, baseEnd_6494826] using wordTrace_append hprefix tailTrace_6494826
  have hstable : (prefixWord ++ tailWord_6494826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494826).length < 2 ^ (prefixWord ++ tailWord_6494826).sum := by decide
  have hdescent : baseEnd_6494826 < baseStart_6494826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494829 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 1, 1, 6]
def baseStart_6494829 : Nat := 118140960795 + 6494829 * 2 ^ 59
def prefixEnd_6494829 : Nat := 4983230072969 + 3 ^ 40 * 6494829 * 2
def baseEnd_6494829 : Nat := 3334969045760274685368331

theorem tailTrace_6494829 : CollatzResearch.WordTrace tailWord_6494829 prefixEnd_6494829 3334969045760274685368331 := by
  unfold tailWord_6494829
  simp only [CollatzResearch.WordTrace]
  refine ⟨236885874587351236328119541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157923916391567490885413027 236885874587351236328119541)
  ·
    refine ⟨22208050742564178405761207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 236885874587351236328119541 22208050742564178405761207)
    ·
      refine ⟨33312076113846267608641811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22208050742564178405761207 33312076113846267608641811)
      ·
        refine ⟨49968114170769401412962717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33312076113846267608641811 49968114170769401412962717)
        ·
          refine ⟨18738042814038525529861019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49968114170769401412962717 18738042814038525529861019)
          ·
            refine ⟨28107064221057788294791529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18738042814038525529861019 28107064221057788294791529)
            ·
              refine ⟨21080298165793341221093647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28107064221057788294791529 21080298165793341221093647)
              ·
                refine ⟨31620447248690011831640471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21080298165793341221093647 31620447248690011831640471)
                ·
                  refine ⟨47430670873035017747460707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31620447248690011831640471 47430670873035017747460707)
                  ·
                    refine ⟨71146006309552526621191061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47430670873035017747460707 71146006309552526621191061)
                    ·
                      refine ⟨3334969045760274685368331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71146006309552526621191061 3334969045760274685368331)
                      ·
                        rfl

theorem cell23_6494829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_6494829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494829 prefixEnd_6494829 := by exact prefixLift 6494829
  have htrace : WordTrace (prefixWord ++ tailWord_6494829) baseStart_6494829 baseEnd_6494829 := by
    simpa [prefixWord, tailWord_6494829, baseEnd_6494829] using wordTrace_append hprefix tailTrace_6494829
  have hstable : (prefixWord ++ tailWord_6494829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494829).length < 2 ^ (prefixWord ++ tailWord_6494829).sum := by decide
  have hdescent : baseEnd_6494829 < baseStart_6494829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494853 : List Nat := [1, 3, 1, 1, 4, 3, 3, 1, 1, 2, 3]
def baseStart_6494853 : Nat := 118140960795 + 6494853 * 2 ^ 59
def prefixEnd_6494853 : Nat := 4983230072969 + 3 ^ 40 * 6494853 * 2
def baseEnd_6494853 : Nat := 3334981369295982591468221

theorem tailTrace_6494853 : CollatzResearch.WordTrace tailWord_6494853 prefixEnd_6494853 3334981369295982591468221 := by
  unfold tailWord_6494853
  simp only [CollatzResearch.WordTrace]
  refine ⟨236886749939264288426993213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157924499959509525617995475 236886749939264288426993213)
  ·
    refine ⟨88832531227224108160122455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 236886749939264288426993213 88832531227224108160122455)
    ·
      refine ⟨133248796840836162240183683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88832531227224108160122455 133248796840836162240183683)
      ·
        refine ⟨199873195261254243360275525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133248796840836162240183683 199873195261254243360275525)
        ·
          refine ⟨37476224111485170630051661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 199873195261254243360275525 37476224111485170630051661)
          ·
            refine ⟨14053584041806938986269373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37476224111485170630051661 14053584041806938986269373)
            ·
              refine ⟨5270094015677602119851015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14053584041806938986269373 5270094015677602119851015)
              ·
                refine ⟨7905141023516403179776523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5270094015677602119851015 7905141023516403179776523)
                ·
                  refine ⟨11857711535274604769664785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7905141023516403179776523 11857711535274604769664785)
                  ·
                    refine ⟨8893283651455953577248589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11857711535274604769664785 8893283651455953577248589)
                    ·
                      refine ⟨3334981369295982591468221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8893283651455953577248589 3334981369295982591468221)
                      ·
                        rfl

theorem cell23_6494853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 1, 1, 2, 3].length) (baseStart_6494853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494853 prefixEnd_6494853 := by exact prefixLift 6494853
  have htrace : WordTrace (prefixWord ++ tailWord_6494853) baseStart_6494853 baseEnd_6494853 := by
    simpa [prefixWord, tailWord_6494853, baseEnd_6494853] using wordTrace_append hprefix tailTrace_6494853
  have hstable : (prefixWord ++ tailWord_6494853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494853).length < 2 ^ (prefixWord ++ tailWord_6494853).sum := by decide
  have hdescent : baseEnd_6494853 < baseStart_6494853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494893 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_6494893 : Nat := 118140960795 + 6494893 * 2 ^ 59
def prefixEnd_6494893 : Nat := 4983230072969 + 3 ^ 40 * 6494893 * 2
def baseEnd_6494893 : Nat := 3335001908522162434968037

theorem tailTrace_6494893 : CollatzResearch.WordTrace tailWord_6494893 prefixEnd_6494893 3335001908522162434968037 := by
  unfold tailWord_6494893
  simp only [CollatzResearch.WordTrace]
  refine ⟨236888208859119375258449333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 157925472572746250172299555 236888208859119375258449333)
  ·
    refine ⟨22208269580542441430479625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 236888208859119375258449333 22208269580542441430479625)
    ·
      refine ⟨16656202185406831072859719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22208269580542441430479625 16656202185406831072859719)
      ·
        refine ⟨24984303278110246609289579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16656202185406831072859719 24984303278110246609289579)
        ·
          refine ⟨37476454917165369913934369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24984303278110246609289579 37476454917165369913934369)
          ·
            refine ⟨28107341187874027435450777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37476454917165369913934369 28107341187874027435450777)
            ·
              refine ⟨21080505890905520576588083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28107341187874027435450777 21080505890905520576588083)
              ·
                refine ⟨31620758836358280864882125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21080505890905520576588083 31620758836358280864882125)
                ·
                  refine ⟨11857784563634355324330797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31620758836358280864882125 11857784563634355324330797)
                  ·
                    refine ⟨4446669211362883246624049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11857784563634355324330797 4446669211362883246624049)
                    ·
                      refine ⟨3335001908522162434968037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446669211362883246624049 3335001908522162434968037)
                      ·
                        rfl

theorem cell23_6494893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_6494893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494893 prefixEnd_6494893 := by exact prefixLift 6494893
  have htrace : WordTrace (prefixWord ++ tailWord_6494893) baseStart_6494893 baseEnd_6494893 := by
    simpa [prefixWord, tailWord_6494893, baseEnd_6494893] using wordTrace_append hprefix tailTrace_6494893
  have hstable : (prefixWord ++ tailWord_6494893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494893).length < 2 ^ (prefixWord ++ tailWord_6494893).sum := by decide
  have hdescent : baseEnd_6494893 < baseStart_6494893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6494906 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2]
def baseStart_6494906 : Nat := 118140960795 + 6494906 * 2 ^ 59
def prefixEnd_6494906 : Nat := 4983230072969 + 3 ^ 40 * 6494906 * 2
def baseEnd_6494906 : Nat := 3335008583770670884105477

theorem tailTrace_6494906 : CollatzResearch.WordTrace tailWord_6494906 prefixEnd_6494906 3335008583770670884105477 := by
  unfold tailWord_6494906
  simp only [CollatzResearch.WordTrace]
  refine ⟨59222170752018069619668143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 157925788672048185652448381 59222170752018069619668143)
  ·
    refine ⟨88833256128027104429502215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59222170752018069619668143 88833256128027104429502215)
    ·
      refine ⟨133249884192040656644253323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 88833256128027104429502215 133249884192040656644253323)
      ·
        refine ⟨199874826288060984966379985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133249884192040656644253323 199874826288060984966379985)
        ·
          refine ⟨149906119716045738724784989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 199874826288060984966379985 149906119716045738724784989)
          ·
            refine ⟨56214794893517152021794371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 149906119716045738724784989 56214794893517152021794371)
            ·
              refine ⟨84322192340275728032691557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56214794893517152021794371 84322192340275728032691557)
              ·
                refine ⟨15810411063801699006129667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84322192340275728032691557 15810411063801699006129667)
                ·
                  refine ⟨23715616595702548509194501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15810411063801699006129667 23715616595702548509194501)
                  ·
                    refine ⟨4446678111694227845473969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23715616595702548509194501 4446678111694227845473969)
                    ·
                      refine ⟨3335008583770670884105477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4446678111694227845473969 3335008583770670884105477)
                      ·
                        rfl

theorem cell23_6494906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2].length) (baseStart_6494906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6494906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6494906 prefixEnd_6494906 := by exact prefixLift 6494906
  have htrace : WordTrace (prefixWord ++ tailWord_6494906) baseStart_6494906 baseEnd_6494906 := by
    simpa [prefixWord, tailWord_6494906, baseEnd_6494906] using wordTrace_append hprefix tailTrace_6494906
  have hstable : (prefixWord ++ tailWord_6494906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6494906).length < 2 ^ (prefixWord ++ tailWord_6494906).sum := by decide
  have hdescent : baseEnd_6494906 < baseStart_6494906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6494906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
