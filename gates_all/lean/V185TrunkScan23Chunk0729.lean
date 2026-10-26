import V185TrunkScan23Chunk0728

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4311933 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 4, 4]
def baseStart_4311933 : Nat := 118140960795 + 4311933 * 2 ^ 59
def prefixEnd_4311933 : Nat := 4983230072969 + 3 ^ 40 * 4311933 * 2
def baseEnd_4311933 : Nat := 738031392994461092002429

theorem tailTrace_4311933 : CollatzResearch.WordTrace tailWord_4311933 prefixEnd_4311933 738031392994461092002429 := by
  unfold tailWord_4311933
  simp only [CollatzResearch.WordTrace]
  refine ⟨157269116687610635372156453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104846077791740423581437635 157269116687610635372156453)
  ·
    refine ⟨29487959378926994132279335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157269116687610635372156453 29487959378926994132279335)
    ·
      refine ⟨44231939068390491198419003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29487959378926994132279335 44231939068390491198419003)
      ·
        refine ⟨66347908602585736797628505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44231939068390491198419003 66347908602585736797628505)
        ·
          refine ⟨49760931451939302598221379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66347908602585736797628505 49760931451939302598221379)
          ·
            refine ⟨74641397177908953897332069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49760931451939302598221379 74641397177908953897332069)
            ·
              refine ⟨13995261970857928855749763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74641397177908953897332069 13995261970857928855749763)
              ·
                refine ⟨20992892956286893283624645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13995261970857928855749763 20992892956286893283624645)
                ·
                  refine ⟨3936167429303792490679621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20992892956286893283624645 3936167429303792490679621)
                  ·
                    refine ⟨738031392994461092002429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3936167429303792490679621 738031392994461092002429)
                    ·
                      rfl

theorem cell23_4311933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_4311933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311933 prefixEnd_4311933 := by exact prefixLift 4311933
  have htrace : WordTrace (prefixWord ++ tailWord_4311933) baseStart_4311933 baseEnd_4311933 := by
    simpa [prefixWord, tailWord_4311933, baseEnd_4311933] using wordTrace_append hprefix tailTrace_4311933
  have hstable : (prefixWord ++ tailWord_4311933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311933).length < 2 ^ (prefixWord ++ tailWord_4311933).sum := by decide
  have hdescent : baseEnd_4311933 < baseStart_4311933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311936 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 4]
def baseStart_4311936 : Nat := 118140960795 + 4311936 * 2 ^ 59
def prefixEnd_4311936 : Nat := 4983230072969 + 3 ^ 40 * 4311936 * 2
def baseEnd_4311936 : Nat := 2214095719425346764269773

theorem tailTrace_4311936 : CollatzResearch.WordTrace tailWord_4311936 prefixEnd_4311936 2214095719425346764269773 := by
  unfold tailWord_4311936
  simp only [CollatzResearch.WordTrace]
  refine ⟨78634613053299883442257831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104846150737733177923010441 78634613053299883442257831)
  ·
    refine ⟨117951919579949825163386747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78634613053299883442257831 117951919579949825163386747)
    ·
      refine ⟨176927879369924737745080121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117951919579949825163386747 176927879369924737745080121)
      ·
        refine ⟨132695909527443553308810091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176927879369924737745080121 132695909527443553308810091)
        ·
          refine ⟨199043864291165329963215137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132695909527443553308810091 199043864291165329963215137)
          ·
            refine ⟨149282898218373997472411353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199043864291165329963215137 149282898218373997472411353)
            ·
              refine ⟨111962173663780498104308515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149282898218373997472411353 111962173663780498104308515)
              ·
                refine ⟨167943260495670747156462773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111962173663780498104308515 167943260495670747156462773)
                ·
                  refine ⟨15744680671469132545918385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 167943260495670747156462773 15744680671469132545918385)
                  ·
                    refine ⟨11808510503601849409438789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15744680671469132545918385 11808510503601849409438789)
                    ·
                      refine ⟨2214095719425346764269773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11808510503601849409438789 2214095719425346764269773)
                      ·
                        rfl

theorem cell23_4311936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_4311936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311936 prefixEnd_4311936 := by exact prefixLift 4311936
  have htrace : WordTrace (prefixWord ++ tailWord_4311936) baseStart_4311936 baseEnd_4311936 := by
    simpa [prefixWord, tailWord_4311936, baseEnd_4311936] using wordTrace_append hprefix tailTrace_4311936
  have hstable : (prefixWord ++ tailWord_4311936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311936).length < 2 ^ (prefixWord ++ tailWord_4311936).sum := by decide
  have hdescent : baseEnd_4311936 < baseStart_4311936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311943 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_4311943 : Nat := 118140960795 + 4311943 * 2 ^ 59
def prefixEnd_4311943 : Nat := 4983230072969 + 3 ^ 40 * 4311943 * 2
def baseEnd_4311943 : Nat := 2214099313789928236882241

theorem tailTrace_4311943 : CollatzResearch.WordTrace tailWord_4311943 prefixEnd_4311943 2214099313789928236882241 := by
  unfold tailWord_4311943
  simp only [CollatzResearch.WordTrace]
  refine ⟨157269481417574407080020483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104846320945049604720013655 157269481417574407080020483)
  ·
    refine ⟨235904222126361610620030725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157269481417574407080020483 235904222126361610620030725)
    ·
      refine ⟨44232041648692801991255761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235904222126361610620030725 44232041648692801991255761)
      ·
        refine ⟨33174031236519601493441821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44232041648692801991255761 33174031236519601493441821)
        ·
          refine ⟨12440261713694850560040683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33174031236519601493441821 12440261713694850560040683)
          ·
            refine ⟨18660392570542275840061025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12440261713694850560040683 18660392570542275840061025)
            ·
              refine ⟨13995294427906706880045769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18660392570542275840061025 13995294427906706880045769)
              ·
                refine ⟨10496470820930030160034327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13995294427906706880045769 10496470820930030160034327)
                ·
                  refine ⟨15744706231395045240051491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10496470820930030160034327 15744706231395045240051491)
                  ·
                    refine ⟨23617059347092567860077237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15744706231395045240051491 23617059347092567860077237)
                    ·
                      refine ⟨2214099313789928236882241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23617059347092567860077237 2214099313789928236882241)
                      ·
                        rfl

theorem cell23_4311943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_4311943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311943 prefixEnd_4311943 := by exact prefixLift 4311943
  have htrace : WordTrace (prefixWord ++ tailWord_4311943) baseStart_4311943 baseEnd_4311943 := by
    simpa [prefixWord, tailWord_4311943, baseEnd_4311943] using wordTrace_append hprefix tailTrace_4311943
  have hstable : (prefixWord ++ tailWord_4311943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311943).length < 2 ^ (prefixWord ++ tailWord_4311943).sum := by decide
  have hdescent : baseEnd_4311943 < baseStart_4311943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311954 : List Nat := [3, 2, 3, 2, 3, 1, 1, 2, 1, 5]
def baseStart_4311954 : Nat := 118140960795 + 4311954 * 2 ^ 59
def prefixEnd_4311954 : Nat := 4983230072969 + 3 ^ 40 * 4311954 * 2
def baseEnd_4311954 : Nat := 738034987359042564614897

theorem tailTrace_4311954 : CollatzResearch.WordTrace tailWord_4311954 prefixEnd_4311954 738034987359042564614897 := by
  unfold tailWord_4311954
  simp only [CollatzResearch.WordTrace]
  refine ⟨39317470655133638989667729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104846588413689703972447277 39317470655133638989667729)
  ·
    refine ⟨29488102991350229242250797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39317470655133638989667729 29488102991350229242250797)
    ·
      refine ⟨11058038621756335965844049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29488102991350229242250797 11058038621756335965844049)
      ·
        refine ⟨8293528966317251974383037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11058038621756335965844049 8293528966317251974383037)
        ·
          refine ⟨3110073362368969490393639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8293528966317251974383037 3110073362368969490393639)
          ·
            refine ⟨4665110043553454235590459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3110073362368969490393639 4665110043553454235590459)
            ·
              refine ⟨6997665065330181353385689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4665110043553454235590459 6997665065330181353385689)
              ·
                refine ⟨5248248798997636015039267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6997665065330181353385689 5248248798997636015039267)
                ·
                  refine ⟨7872373198496454022558901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5248248798997636015039267 7872373198496454022558901)
                  ·
                    refine ⟨738034987359042564614897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7872373198496454022558901 738034987359042564614897)
                    ·
                      rfl

theorem cell23_4311954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_4311954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311954 prefixEnd_4311954 := by exact prefixLift 4311954
  have htrace : WordTrace (prefixWord ++ tailWord_4311954) baseStart_4311954 baseEnd_4311954 := by
    simpa [prefixWord, tailWord_4311954, baseEnd_4311954] using wordTrace_append hprefix tailTrace_4311954
  have hstable : (prefixWord ++ tailWord_4311954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311954).length < 2 ^ (prefixWord ++ tailWord_4311954).sum := by decide
  have hdescent : baseEnd_4311954 < baseStart_4311954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311970 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_4311970 : Nat := 118140960795 + 4311970 * 2 ^ 59
def prefixEnd_4311970 : Nat := 4983230072969 + 3 ^ 40 * 4311970 * 2
def baseEnd_4311970 : Nat := 2214113177767599631244617

theorem tailTrace_4311970 : CollatzResearch.WordTrace tailWord_4311970 prefixEnd_4311970 2214113177767599631244617 := by
  unfold tailWord_4311970
  simp only [CollatzResearch.WordTrace]
  refine ⟨39317616547119147672813341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104846977458984393794168909 39317616547119147672813341)
  ·
    refine ⟨14744106205169680377305003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39317616547119147672813341 14744106205169680377305003)
    ·
      refine ⟨22116159307754520565957505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14744106205169680377305003 22116159307754520565957505)
      ·
        refine ⟨16587119480815890424468129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22116159307754520565957505 16587119480815890424468129)
        ·
          refine ⟨12440339610611917818351097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16587119480815890424468129 12440339610611917818351097)
          ·
            refine ⟨9330254707958938363763323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12440339610611917818351097 9330254707958938363763323)
            ·
              refine ⟨13995382061938407545644985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9330254707958938363763323 13995382061938407545644985)
              ·
                refine ⟨10496536546453805659233739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13995382061938407545644985 10496536546453805659233739)
                ·
                  refine ⟨15744804819680708488850609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10496536546453805659233739 15744804819680708488850609)
                  ·
                    refine ⟨11808603614760531366637957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15744804819680708488850609 11808603614760531366637957)
                    ·
                      refine ⟨2214113177767599631244617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11808603614760531366637957 2214113177767599631244617)
                      ·
                        rfl

theorem cell23_4311970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_4311970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311970 prefixEnd_4311970 := by exact prefixLift 4311970
  have htrace : WordTrace (prefixWord ++ tailWord_4311970) baseStart_4311970 baseEnd_4311970 := by
    simpa [prefixWord, tailWord_4311970, baseEnd_4311970] using wordTrace_append hprefix tailTrace_4311970
  have hstable : (prefixWord ++ tailWord_4311970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311970).length < 2 ^ (prefixWord ++ tailWord_4311970).sum := by decide
  have hdescent : baseEnd_4311970 < baseStart_4311970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4311986 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_4311986 : Nat := 118140960795 + 4311986 * 2 ^ 59
def prefixEnd_4311986 : Nat := 4983230072969 + 3 ^ 40 * 4311986 * 2
def baseEnd_4311986 : Nat := 2214121393458071568644543

theorem tailTrace_4311986 : CollatzResearch.WordTrace tailWord_4311986 prefixEnd_4311986 2214121393458071568644543 := by
  unfold tailWord_4311986
  simp only [CollatzResearch.WordTrace]
  refine ⟨39317762439104656355958953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104847366504279083615890541 39317762439104656355958953)
  ·
    refine ⟨29488321829328492266969215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39317762439104656355958953 29488321829328492266969215)
    ·
      refine ⟨44232482743992738400453823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29488321829328492266969215 44232482743992738400453823)
      ·
        refine ⟨66348724115989107600680735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44232482743992738400453823 66348724115989107600680735)
        ·
          refine ⟨99523086173983661401021103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66348724115989107600680735 99523086173983661401021103)
          ·
            refine ⟨149284629260975492101531655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99523086173983661401021103 149284629260975492101531655)
            ·
              refine ⟨223926943891463238152297483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149284629260975492101531655 223926943891463238152297483)
              ·
                refine ⟨335890415837194857228446225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223926943891463238152297483 335890415837194857228446225)
                ·
                  refine ⟨251917811877896142921334669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335890415837194857228446225 251917811877896142921334669)
                  ·
                    refine ⟨94469179454211053595500501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 251917811877896142921334669 94469179454211053595500501)
                    ·
                      refine ⟨2214121393458071568644543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94469179454211053595500501 2214121393458071568644543)
                      ·
                        rfl

theorem cell23_4311986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_4311986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4311986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4311986 prefixEnd_4311986 := by exact prefixLift 4311986
  have htrace : WordTrace (prefixWord ++ tailWord_4311986) baseStart_4311986 baseEnd_4311986 := by
    simpa [prefixWord, tailWord_4311986, baseEnd_4311986] using wordTrace_append hprefix tailTrace_4311986
  have hstable : (prefixWord ++ tailWord_4311986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4311986).length < 2 ^ (prefixWord ++ tailWord_4311986).sum := by decide
  have hdescent : baseEnd_4311986 < baseStart_4311986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4311986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312000 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 3, 3, 2]
def baseStart_4312000 : Nat := 118140960795 + 4312000 * 2 ^ 59
def prefixEnd_4312000 : Nat := 4983230072969 + 3 ^ 40 * 4312000 * 2
def baseEnd_4312000 : Nat := 2214128582187234513869479

theorem tailTrace_4312000 : CollatzResearch.WordTrace tailWord_4312000 prefixEnd_4312000 2214128582187234513869479 := by
  unfold tailWord_4312000
  simp only [CollatzResearch.WordTrace]
  refine ⟨78635780189183952907422727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104847706918911937209896969 78635780189183952907422727)
  ·
    refine ⟨117953670283775929361134091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78635780189183952907422727 117953670283775929361134091)
    ·
      refine ⟨176930505425663894041701137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117953670283775929361134091 176930505425663894041701137)
      ·
        refine ⟨132697879069247920531275853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176930505425663894041701137 132697879069247920531275853)
        ·
          refine ⟨49761704650967970199228445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132697879069247920531275853 49761704650967970199228445)
          ·
            refine ⟨18660639244112988824710667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49761704650967970199228445 18660639244112988824710667)
            ·
              refine ⟨27990958866169483237066001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18660639244112988824710667 27990958866169483237066001)
              ·
                refine ⟨20993219149627112427799501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27990958866169483237066001 20993219149627112427799501)
                ·
                  refine ⟨7872457181110167160424813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20993219149627112427799501 7872457181110167160424813)
                  ·
                    refine ⟨2952171442916312685159305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7872457181110167160424813 2952171442916312685159305)
                    ·
                      refine ⟨2214128582187234513869479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2952171442916312685159305 2214128582187234513869479)
                      ·
                        rfl

theorem cell23_4312000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 3, 3, 2].length) (baseStart_4312000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312000 prefixEnd_4312000 := by exact prefixLift 4312000
  have htrace : WordTrace (prefixWord ++ tailWord_4312000) baseStart_4312000 baseEnd_4312000 := by
    simpa [prefixWord, tailWord_4312000, baseEnd_4312000] using wordTrace_append hprefix tailTrace_4312000
  have hstable : (prefixWord ++ tailWord_4312000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312000).length < 2 ^ (prefixWord ++ tailWord_4312000).sum := by decide
  have hdescent : baseEnd_4312000 < baseStart_4312000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312047 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 4, 2, 2]
def baseStart_4312047 : Nat := 118140960795 + 4312047 * 2 ^ 59
def prefixEnd_4312047 : Nat := 4983230072969 + 3 ^ 40 * 4312047 * 2
def baseEnd_4312047 : Nat := 2214152715777995829981763

theorem tailTrace_4312047 : CollatzResearch.WordTrace tailWord_4312047 prefixEnd_4312047 2214152715777995829981763 := by
  unfold tailWord_4312047
  simp only [CollatzResearch.WordTrace]
  refine ⟨157273274609197632841806395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104848849739465088561204263 157273274609197632841806395)
  ·
    refine ⟨235909911913796449262709593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157273274609197632841806395 235909911913796449262709593)
    ·
      refine ⟨176932433935347336947032195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235909911913796449262709593 176932433935347336947032195)
      ·
        refine ⟨265398650903021005420548293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176932433935347336947032195 265398650903021005420548293)
        ·
          refine ⟨49762247044316438516352805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 265398650903021005420548293 49762247044316438516352805)
          ·
            refine ⟨9330421320809332221816151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49762247044316438516352805 9330421320809332221816151)
            ·
              refine ⟨13995631981213998332724227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9330421320809332221816151 13995631981213998332724227)
              ·
                refine ⟨20993447971820997499086341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13995631981213998332724227 20993447971820997499086341)
                ·
                  refine ⟨3936271494716437031078689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20993447971820997499086341 3936271494716437031078689)
                  ·
                    refine ⟨2952203621037327773309017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3936271494716437031078689 2952203621037327773309017)
                    ·
                      refine ⟨2214152715777995829981763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2952203621037327773309017 2214152715777995829981763)
                      ·
                        rfl

theorem cell23_4312047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 2, 2].length) (baseStart_4312047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312047 prefixEnd_4312047 := by exact prefixLift 4312047
  have htrace : WordTrace (prefixWord ++ tailWord_4312047) baseStart_4312047 baseEnd_4312047 := by
    simpa [prefixWord, tailWord_4312047, baseEnd_4312047] using wordTrace_append hprefix tailTrace_4312047
  have hstable : (prefixWord ++ tailWord_4312047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312047).length < 2 ^ (prefixWord ++ tailWord_4312047).sum := by decide
  have hdescent : baseEnd_4312047 < baseStart_4312047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312083 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 2, 5]
def baseStart_4312083 : Nat := 118140960795 + 4312083 * 2 ^ 59
def prefixEnd_4312083 : Nat := 4983230072969 + 3 ^ 40 * 4312083 * 2
def baseEnd_4312083 : Nat := 738057067027185896377199

theorem tailTrace_4312083 : CollatzResearch.WordTrace tailWord_4312083 prefixEnd_4312083 738057067027185896377199 := by
  unfold tailWord_4312083
  simp only [CollatzResearch.WordTrace]
  refine ⟨157274587637067210990116903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104849725091378140660077935 157274587637067210990116903)
  ·
    refine ⟨235911881455600816485175355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157274587637067210990116903 235911881455600816485175355)
    ·
      refine ⟨353867822183401224727763033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235911881455600816485175355 353867822183401224727763033)
      ·
        refine ⟨265400866637550918545822275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353867822183401224727763033 265400866637550918545822275)
        ·
          refine ⟨398101299956326377818733413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265400866637550918545822275 398101299956326377818733413)
          ·
            refine ⟨74643993741811195841012515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 398101299956326377818733413 74643993741811195841012515)
            ·
              refine ⟨111965990612716793761518773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74643993741811195841012515 111965990612716793761518773)
              ·
                refine ⟨10496811619942199415142385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111965990612716793761518773 10496811619942199415142385)
                ·
                  refine ⟨7872608714956649561356789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10496811619942199415142385 7872608714956649561356789)
                  ·
                    refine ⟨738057067027185896377199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7872608714956649561356789 738057067027185896377199)
                    ·
                      rfl

theorem cell23_4312083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 5].length) (baseStart_4312083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312083 prefixEnd_4312083 := by exact prefixLift 4312083
  have htrace : WordTrace (prefixWord ++ tailWord_4312083) baseStart_4312083 baseEnd_4312083 := by
    simpa [prefixWord, tailWord_4312083, baseEnd_4312083] using wordTrace_append hprefix tailTrace_4312083
  have hstable : (prefixWord ++ tailWord_4312083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312083).length < 2 ^ (prefixWord ++ tailWord_4312083).sum := by decide
  have hdescent : baseEnd_4312083 < baseStart_4312083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312087 : List Nat := [1, 1, 3, 5, 1, 1, 3, 3, 5]
def baseStart_4312087 : Nat := 118140960795 + 4312087 * 2 ^ 59
def prefixEnd_4312087 : Nat := 4983230072969 + 3 ^ 40 * 4312087 * 2
def baseEnd_4312087 : Nat := 246019250556019519275731

theorem tailTrace_4312087 : CollatzResearch.WordTrace tailWord_4312087 prefixEnd_4312087 246019250556019519275731 := by
  unfold tailWord_4312087
  simp only [CollatzResearch.WordTrace]
  refine ⟨157274733529052719673262515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104849822352701813115508343 157274733529052719673262515)
  ·
    refine ⟨235912100293579079509893773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157274733529052719673262515 235912100293579079509893773)
    ·
      refine ⟨88467037610092154816210165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235912100293579079509893773 88467037610092154816210165)
      ·
        refine ⟨8293784775946139514019703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 88467037610092154816210165 8293784775946139514019703)
        ·
          refine ⟨12440677163919209271029555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8293784775946139514019703 12440677163919209271029555)
          ·
            refine ⟨18661015745878813906544333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12440677163919209271029555 18661015745878813906544333)
            ·
              refine ⟨6997880904704555214954125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18661015745878813906544333 6997880904704555214954125)
              ·
                refine ⟨2624205339264208205607797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6997880904704555214954125 2624205339264208205607797)
                ·
                  refine ⟨246019250556019519275731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2624205339264208205607797 246019250556019519275731)
                  ·
                    rfl

theorem cell23_4312087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 3, 3, 5].length) (baseStart_4312087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312087 prefixEnd_4312087 := by exact prefixLift 4312087
  have htrace : WordTrace (prefixWord ++ tailWord_4312087) baseStart_4312087 baseEnd_4312087 := by
    simpa [prefixWord, tailWord_4312087, baseEnd_4312087] using wordTrace_append hprefix tailTrace_4312087
  have hstable : (prefixWord ++ tailWord_4312087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312087).length < 2 ^ (prefixWord ++ tailWord_4312087).sum := by decide
  have hdescent : baseEnd_4312087 < baseStart_4312087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312100 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 4, 5]
def baseStart_4312100 : Nat := 118140960795 + 4312100 * 2 ^ 59
def prefixEnd_4312100 : Nat := 4983230072969 + 3 ^ 40 * 4312100 * 2
def baseEnd_4312100 : Nat := 738059976750894707539673

theorem tailTrace_4312100 : CollatzResearch.WordTrace tailWord_4312100 prefixEnd_4312100 738059976750894707539673 := by
  unfold tailWord_4312100
  simp only [CollatzResearch.WordTrace]
  refine ⟨78637603839002811446742877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104850138452003748595657169 78637603839002811446742877)
  ·
    refine ⟨29489101439626054292528579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78637603839002811446742877 29489101439626054292528579)
    ·
      refine ⟨44233652159439081438792869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29489101439626054292528579 44233652159439081438792869)
      ·
        refine ⟨8293809779894827769773663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44233652159439081438792869 8293809779894827769773663)
        ·
          refine ⟨12440714669842241654660495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8293809779894827769773663 12440714669842241654660495)
          ·
            refine ⟨18661072004763362481990743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12440714669842241654660495 18661072004763362481990743)
            ·
              refine ⟨27991608007145043722986115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18661072004763362481990743 27991608007145043722986115)
              ·
                refine ⟨41987412010717565584479173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27991608007145043722986115 41987412010717565584479173)
                ·
                  refine ⟨7872639752009543547089845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 41987412010717565584479173 7872639752009543547089845)
                  ·
                    refine ⟨738059976750894707539673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7872639752009543547089845 738059976750894707539673)
                    ·
                      rfl

theorem cell23_4312100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_4312100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312100 prefixEnd_4312100 := by exact prefixLift 4312100
  have htrace : WordTrace (prefixWord ++ tailWord_4312100) baseStart_4312100 baseEnd_4312100 := by
    simpa [prefixWord, tailWord_4312100, baseEnd_4312100] using wordTrace_append hprefix tailTrace_4312100
  have hstable : (prefixWord ++ tailWord_4312100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312100).length < 2 ^ (prefixWord ++ tailWord_4312100).sum := by decide
  have hdescent : baseEnd_4312100 < baseStart_4312100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312110 : List Nat := [4, 1, 3, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_4312110 : Nat := 118140960795 + 4312110 * 2 ^ 59
def prefixEnd_4312110 : Nat := 4983230072969 + 3 ^ 40 * 4312110 * 2
def baseEnd_4312110 : Nat := 2214185065059229083493973

theorem tailTrace_4312110 : CollatzResearch.WordTrace tailWord_4312110 prefixEnd_4312110 2214185065059229083493973 := by
  unfold tailWord_4312110
  simp only [CollatzResearch.WordTrace]
  refine ⟨19659446550996174325168723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104850381605312929734233189 19659446550996174325168723)
  ·
    refine ⟨29489169826494261487753085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19659446550996174325168723 29489169826494261487753085)
    ·
      refine ⟨11058438684935348057907407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29489169826494261487753085 11058438684935348057907407)
      ·
        refine ⟨16587658027403022086861111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11058438684935348057907407 16587658027403022086861111)
        ·
          refine ⟨24881487041104533130291667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16587658027403022086861111 24881487041104533130291667)
          ·
            refine ⟨37322230561656799695437501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24881487041104533130291667 37322230561656799695437501)
            ·
              refine ⟨13995836460621299885789063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37322230561656799695437501 13995836460621299885789063)
              ·
                refine ⟨20993754690931949828683595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13995836460621299885789063 20993754690931949828683595)
                ·
                  refine ⟨31490632036397924743025393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20993754690931949828683595 31490632036397924743025393)
                  ·
                    refine ⟨23617974027298443557269045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31490632036397924743025393 23617974027298443557269045)
                    ·
                      refine ⟨2214185065059229083493973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23617974027298443557269045 2214185065059229083493973)
                      ·
                        rfl

theorem cell23_4312110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_4312110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312110 prefixEnd_4312110 := by exact prefixLift 4312110
  have htrace : WordTrace (prefixWord ++ tailWord_4312110) baseStart_4312110 baseEnd_4312110 := by
    simpa [prefixWord, tailWord_4312110, baseEnd_4312110] using wordTrace_append hprefix tailTrace_4312110
  have hstable : (prefixWord ++ tailWord_4312110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312110).length < 2 ^ (prefixWord ++ tailWord_4312110).sum := by decide
  have hdescent : baseEnd_4312110 < baseStart_4312110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312133 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 2, 4, 4]
def baseStart_4312133 : Nat := 118140960795 + 4312133 * 2 ^ 59
def prefixEnd_4312133 : Nat := 4983230072969 + 3 ^ 40 * 4312133 * 2
def baseEnd_4312133 : Nat := 2214196875114282493506367

theorem tailTrace_4312133 : CollatzResearch.WordTrace tailWord_4312133 prefixEnd_4312133 2214196875114282493506367 := by
  unfold tailWord_4312133
  simp only [CollatzResearch.WordTrace]
  refine ⟨157276411286886069529437053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104850940857924046352958035 157276411286886069529437053)
  ·
    refine ⟨58978654232582276073538895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157276411286886069529437053 58978654232582276073538895)
    ·
      refine ⟨88467981348873414110308343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58978654232582276073538895 88467981348873414110308343)
      ·
        refine ⟨132701972023310121165462515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88467981348873414110308343 132701972023310121165462515)
        ·
          refine ⟨199052958034965181748193773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132701972023310121165462515 199052958034965181748193773)
          ·
            refine ⟨74644859263111943155572665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199052958034965181748193773 74644859263111943155572665)
            ·
              refine ⟨55983644447333957366679499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74644859263111943155572665 55983644447333957366679499)
              ·
                refine ⟨83975466671000936050019249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55983644447333957366679499 83975466671000936050019249)
                ·
                  refine ⟨62981600003250702037514437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83975466671000936050019249 62981600003250702037514437)
                  ·
                    refine ⟨11809050000609506632033957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62981600003250702037514437 11809050000609506632033957)
                    ·
                      refine ⟨2214196875114282493506367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11809050000609506632033957 2214196875114282493506367)
                      ·
                        rfl

theorem cell23_4312133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_4312133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312133 prefixEnd_4312133 := by exact prefixLift 4312133
  have htrace : WordTrace (prefixWord ++ tailWord_4312133) baseStart_4312133 baseEnd_4312133 := by
    simpa [prefixWord, tailWord_4312133, baseEnd_4312133] using wordTrace_append hprefix tailTrace_4312133
  have hstable : (prefixWord ++ tailWord_4312133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312133).length < 2 ^ (prefixWord ++ tailWord_4312133).sum := by decide
  have hdescent : baseEnd_4312133 < baseStart_4312133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312134 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_4312134 : Nat := 118140960795 + 4312134 * 2 ^ 59
def prefixEnd_4312134 : Nat := 4983230072969 + 3 ^ 40 * 4312134 * 2
def baseEnd_4312134 : Nat := 738065796198312329864621

theorem tailTrace_4312134 : CollatzResearch.WordTrace tailWord_4312134 prefixEnd_4312134 738065796198312329864621 := by
  unfold tailWord_4312134
  simp only [CollatzResearch.WordTrace]
  refine ⟨4914888992496326459381983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 104850965173254964466815637 4914888992496326459381983)
  ·
    refine ⟨7372333488744489689072975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4914888992496326459381983 7372333488744489689072975)
    ·
      refine ⟨11058500233116734533609463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7372333488744489689072975 11058500233116734533609463)
      ·
        refine ⟨16587750349675101800414195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11058500233116734533609463 16587750349675101800414195)
        ·
          refine ⟨24881625524512652700621293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16587750349675101800414195 24881625524512652700621293)
          ·
            refine ⟨9330609571692244762732985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24881625524512652700621293 9330609571692244762732985)
            ·
              refine ⟨6997957178769183572049739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9330609571692244762732985 6997957178769183572049739)
              ·
                refine ⟨10496935768153775358074609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6997957178769183572049739 10496935768153775358074609)
                ·
                  refine ⟨7872701826115331518555957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10496935768153775358074609 7872701826115331518555957)
                  ·
                    refine ⟨738065796198312329864621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7872701826115331518555957 738065796198312329864621)
                    ·
                      rfl

theorem cell23_4312134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_4312134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312134 prefixEnd_4312134 := by exact prefixLift 4312134
  have htrace : WordTrace (prefixWord ++ tailWord_4312134) baseStart_4312134 baseEnd_4312134 := by
    simpa [prefixWord, tailWord_4312134, baseEnd_4312134] using wordTrace_append hprefix tailTrace_4312134
  have hstable : (prefixWord ++ tailWord_4312134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312134).length < 2 ^ (prefixWord ++ tailWord_4312134).sum := by decide
  have hdescent : baseEnd_4312134 < baseStart_4312134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312160 : List Nat := [2, 1, 1, 3, 2, 2, 4, 2, 6]
def baseStart_4312160 : Nat := 118140960795 + 4312160 * 2 ^ 59
def prefixEnd_4312160 : Nat := 4983230072969 + 3 ^ 40 * 4312160 * 2
def baseEnd_4312160 : Nat := 246023415454661543096527

theorem tailTrace_4312160 : CollatzResearch.WordTrace tailWord_4312160 prefixEnd_4312160 246023415454661543096527 := by
  unfold tailWord_4312160
  simp only [CollatzResearch.WordTrace]
  refine ⟨78638698028894126570334967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104851597371858835427113289 78638698028894126570334967)
  ·
    refine ⟨117958047043341189855502451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78638698028894126570334967 117958047043341189855502451)
    ·
      refine ⟨176937070565011784783253677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117958047043341189855502451 176937070565011784783253677)
      ·
        refine ⟨66351401461879419293720129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176937070565011784783253677 66351401461879419293720129)
        ·
          refine ⟨49763551096409564470290097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66351401461879419293720129 49763551096409564470290097)
          ·
            refine ⟨37322663322307173352717573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49763551096409564470290097 37322663322307173352717573)
            ·
              refine ⟨6997999372932595003634545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37322663322307173352717573 6997999372932595003634545)
              ·
                refine ⟨5248499529699446252725909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6997999372932595003634545 5248499529699446252725909)
                ·
                  refine ⟨246023415454661543096527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5248499529699446252725909 246023415454661543096527)
                  ·
                    rfl

theorem cell23_4312160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 6].length) (baseStart_4312160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312160 prefixEnd_4312160 := by exact prefixLift 4312160
  have htrace : WordTrace (prefixWord ++ tailWord_4312160) baseStart_4312160 baseEnd_4312160 := by
    simpa [prefixWord, tailWord_4312160, baseEnd_4312160] using wordTrace_append hprefix tailTrace_4312160
  have hstable : (prefixWord ++ tailWord_4312160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312160).length < 2 ^ (prefixWord ++ tailWord_4312160).sum := by decide
  have hdescent : baseEnd_4312160 < baseStart_4312160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312163 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 6]
def baseStart_4312163 : Nat := 118140960795 + 4312163 * 2 ^ 59
def prefixEnd_4312163 : Nat := 4983230072969 + 3 ^ 40 * 4312163 * 2
def baseEnd_4312163 : Nat := 2214212279533917376131229

theorem tailTrace_4312163 : CollatzResearch.WordTrace tailWord_4312163 prefixEnd_4312163 2214212279533917376131229 := by
  unfold tailWord_4312163
  simp only [CollatzResearch.WordTrace]
  refine ⟨157277505476777384653029143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104851670317851589768686095 157277505476777384653029143)
  ·
    refine ⟨235916258215166076979543715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157277505476777384653029143 235916258215166076979543715)
    ·
      refine ⟨353874387322749115469315573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235916258215166076979543715 353874387322749115469315573)
      ·
        refine ⟨33175723811507729575248335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 353874387322749115469315573 33175723811507729575248335)
        ·
          refine ⟨49763585717261594362872503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33175723811507729575248335 49763585717261594362872503)
          ·
            refine ⟨74645378575892391544308755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49763585717261594362872503 74645378575892391544308755)
            ·
              refine ⟨111968067863838587316463133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74645378575892391544308755 111968067863838587316463133)
              ·
                refine ⟨41988025448939470243673675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111968067863838587316463133 41988025448939470243673675)
                ·
                  refine ⟨62982038173409205365510513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41988025448939470243673675 62982038173409205365510513)
                  ·
                    refine ⟨47236528630056904024132885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 62982038173409205365510513 47236528630056904024132885)
                    ·
                      refine ⟨2214212279533917376131229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47236528630056904024132885 2214212279533917376131229)
                      ·
                        rfl

theorem cell23_4312163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_4312163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312163 prefixEnd_4312163 := by exact prefixLift 4312163
  have htrace : WordTrace (prefixWord ++ tailWord_4312163) baseStart_4312163 baseEnd_4312163 := by
    simpa [prefixWord, tailWord_4312163, baseEnd_4312163] using wordTrace_append hprefix tailTrace_4312163
  have hstable : (prefixWord ++ tailWord_4312163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312163).length < 2 ^ (prefixWord ++ tailWord_4312163).sum := by decide
  have hdescent : baseEnd_4312163 < baseStart_4312163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312183 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 7]
def baseStart_4312183 : Nat := 118140960795 + 4312183 * 2 ^ 59
def prefixEnd_4312183 : Nat := 4983230072969 + 3 ^ 40 * 4312183 * 2
def baseEnd_4312183 : Nat := 2214222549147007297881137

theorem tailTrace_4312183 : CollatzResearch.WordTrace tailWord_4312183 prefixEnd_4312183 2214222549147007297881137 := by
  unfold tailWord_4312183
  simp only [CollatzResearch.WordTrace]
  refine ⟨157278234936704928068757203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104852156624469952045838135 157278234936704928068757203)
  ·
    refine ⟨235917352405057392103135805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157278234936704928068757203 235917352405057392103135805)
    ·
      refine ⟨88469007151896522038675927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235917352405057392103135805 88469007151896522038675927)
      ·
        refine ⟨132703510727844783058013891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88469007151896522038675927 132703510727844783058013891)
        ·
          refine ⟨199055266091767174587020837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132703510727844783058013891 199055266091767174587020837)
          ·
            refine ⟨37322862392206345235066407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 199055266091767174587020837 37322862392206345235066407)
            ·
              refine ⟨55984293588309517852599611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37322862392206345235066407 55984293588309517852599611)
              ·
                refine ⟨83976440382464276778899417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55984293588309517852599611 83976440382464276778899417)
                ·
                  refine ⟨62982330286848207584174563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 83976440382464276778899417 62982330286848207584174563)
                  ·
                    refine ⟨94473495430272311376261845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 62982330286848207584174563 94473495430272311376261845)
                    ·
                      refine ⟨2214222549147007297881137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94473495430272311376261845 2214222549147007297881137)
                      ·
                        rfl

theorem cell23_4312183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_4312183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312183 prefixEnd_4312183 := by exact prefixLift 4312183
  have htrace : WordTrace (prefixWord ++ tailWord_4312183) baseStart_4312183 baseEnd_4312183 := by
    simpa [prefixWord, tailWord_4312183, baseEnd_4312183] using wordTrace_append hprefix tailTrace_4312183
  have hstable : (prefixWord ++ tailWord_4312183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312183).length < 2 ^ (prefixWord ++ tailWord_4312183).sum := by decide
  have hdescent : baseEnd_4312183 < baseStart_4312183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312308 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_4312308 : Nat := 118140960795 + 4312308 * 2 ^ 59
def prefixEnd_4312308 : Nat := 4983230072969 + 3 ^ 40 * 4312308 * 2
def baseEnd_4312308 : Nat := 2214286734228819308818063

theorem tailTrace_4312308 : CollatzResearch.WordTrace tailWord_4312308 prefixEnd_4312308 2214286734228819308818063 := by
  unfold tailWord_4312308
  simp only [CollatzResearch.WordTrace]
  refine ⟨78641397030626037208528789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104855196040834716278038385 78641397030626037208528789)
  ·
    refine ⟨3686315485810595494149787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 78641397030626037208528789 3686315485810595494149787)
    ·
      refine ⟨5529473228715893241224681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3686315485810595494149787 5529473228715893241224681)
      ·
        refine ⟨4147104921536919930918511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5529473228715893241224681 4147104921536919930918511)
        ·
          refine ⟨6220657382305379896377767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4147104921536919930918511 6220657382305379896377767)
          ·
            refine ⟨9330986073458069844566651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6220657382305379896377767 9330986073458069844566651)
            ·
              refine ⟨13996479110187104766849977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9330986073458069844566651 13996479110187104766849977)
              ·
                refine ⟨10497359332640328575137483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13996479110187104766849977 10497359332640328575137483)
                ·
                  refine ⟨15746038998960492862706225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10497359332640328575137483 15746038998960492862706225)
                  ·
                    refine ⟨11809529249220369647029669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15746038998960492862706225 11809529249220369647029669)
                    ·
                      refine ⟨2214286734228819308818063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11809529249220369647029669 2214286734228819308818063)
                      ·
                        rfl

theorem cell23_4312308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_4312308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312308 prefixEnd_4312308 := by exact prefixLift 4312308
  have htrace : WordTrace (prefixWord ++ tailWord_4312308) baseStart_4312308 baseEnd_4312308 := by
    simpa [prefixWord, tailWord_4312308, baseEnd_4312308] using wordTrace_append hprefix tailTrace_4312308
  have hstable : (prefixWord ++ tailWord_4312308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312308).length < 2 ^ (prefixWord ++ tailWord_4312308).sum := by decide
  have hdescent : baseEnd_4312308 < baseStart_4312308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312330 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_4312330 : Nat := 118140960795 + 4312330 * 2 ^ 59
def prefixEnd_4312330 : Nat := 4983230072969 + 3 ^ 40 * 4312330 * 2
def baseEnd_4312330 : Nat := 2214298030803218222742961

theorem tailTrace_4312330 : CollatzResearch.WordTrace tailWord_4312330 prefixEnd_4312330 2214298030803218222742961 := by
  unfold tailWord_4312330
  simp only [CollatzResearch.WordTrace]
  refine ⟨39320899116793093043589611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104855730978114914782905629 39320899116793093043589611)
  ·
    refine ⟨58981348675189639565384417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39320899116793093043589611 58981348675189639565384417)
    ·
      refine ⟨44236011506392229674038313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58981348675189639565384417 44236011506392229674038313)
      ·
        refine ⟨33177008629794172255528735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44236011506392229674038313 33177008629794172255528735)
        ·
          refine ⟨49765512944691258383293103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33177008629794172255528735 49765512944691258383293103)
          ·
            refine ⟨74648269417036887574939655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49765512944691258383293103 74648269417036887574939655)
            ·
              refine ⟨111972404125555331362409483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74648269417036887574939655 111972404125555331362409483)
              ·
                refine ⟨167958606188332997043614225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111972404125555331362409483 167958606188332997043614225)
                ·
                  refine ⟨125968954641249747782710669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167958606188332997043614225 125968954641249747782710669)
                  ·
                    refine ⟨47238357990468655418516501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 125968954641249747782710669 47238357990468655418516501)
                    ·
                      refine ⟨2214298030803218222742961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47238357990468655418516501 2214298030803218222742961)
                      ·
                        rfl

theorem cell23_4312330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_4312330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312330 prefixEnd_4312330 := by exact prefixLift 4312330
  have htrace : WordTrace (prefixWord ++ tailWord_4312330) baseStart_4312330 baseEnd_4312330 := by
    simpa [prefixWord, tailWord_4312330, baseEnd_4312330] using wordTrace_append hprefix tailTrace_4312330
  have hstable : (prefixWord ++ tailWord_4312330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312330).length < 2 ^ (prefixWord ++ tailWord_4312330).sum := by decide
  have hdescent : baseEnd_4312330 < baseStart_4312330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312351 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 1, 4, 2]
def baseStart_4312351 : Nat := 118140960795 + 4312351 * 2 ^ 59
def prefixEnd_4312351 : Nat := 4983230072969 + 3 ^ 40 * 4312351 * 2
def baseEnd_4312351 : Nat := 2214308813896962640580365

theorem tailTrace_4312351 : CollatzResearch.WordTrace tailWord_4312351 prefixEnd_4312351 2214308813896962640580365 := by
  unfold tailWord_4312351
  simp only [CollatzResearch.WordTrace]
  refine ⟨157284362400096292760872907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104856241600064195173915271 157284362400096292760872907)
  ·
    refine ⟨235926543600144439141309361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157284362400096292760872907 235926543600144439141309361)
    ·
      refine ⟨176944907700108329355982021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235926543600144439141309361 176944907700108329355982021)
      ·
        refine ⟨33177170193770311754246629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 176944907700108329355982021 33177170193770311754246629)
        ·
          refine ⟨6220719411331933453921243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33177170193770311754246629 6220719411331933453921243)
          ·
            refine ⟨9331079116997900180881865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6220719411331933453921243 9331079116997900180881865)
            ·
              refine ⟨6998309337748425135661399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9331079116997900180881865 6998309337748425135661399)
              ·
                refine ⟨10497464006622637703492099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6998309337748425135661399 10497464006622637703492099)
                ·
                  refine ⟨15746196009933956555238149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10497464006622637703492099 15746196009933956555238149)
                  ·
                    refine ⟨2952411751862616854107153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15746196009933956555238149 2952411751862616854107153)
                    ·
                      refine ⟨2214308813896962640580365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2952411751862616854107153 2214308813896962640580365)
                      ·
                        rfl

theorem cell23_4312351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_4312351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312351 prefixEnd_4312351 := by exact prefixLift 4312351
  have htrace : WordTrace (prefixWord ++ tailWord_4312351) baseStart_4312351 baseEnd_4312351 := by
    simpa [prefixWord, tailWord_4312351, baseEnd_4312351] using wordTrace_append hprefix tailTrace_4312351
  have hstable : (prefixWord ++ tailWord_4312351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312351).length < 2 ^ (prefixWord ++ tailWord_4312351).sum := by decide
  have hdescent : baseEnd_4312351 < baseStart_4312351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312357 : List Nat := [1, 3, 1, 2, 4, 2, 1, 2, 7]
def baseStart_4312357 : Nat := 118140960795 + 4312357 * 2 ^ 59
def prefixEnd_4312357 : Nat := 4983230072969 + 3 ^ 40 * 4312357 * 2
def baseEnd_4312357 : Nat := 246034654975654401900593

theorem tailTrace_4312357 : CollatzResearch.WordTrace tailWord_4312357 prefixEnd_4312357 246034654975654401900593 := by
  unfold tailWord_4312357
  simp only [CollatzResearch.WordTrace]
  refine ⟨157284581238074555785591325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104856387492049703857060883 157284581238074555785591325)
  ·
    refine ⟨58981717964277958419596747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157284581238074555785591325 58981717964277958419596747)
    ·
      refine ⟨88472576946416937629395121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58981717964277958419596747 88472576946416937629395121)
      ·
        refine ⟨66354432709812703222046341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88472576946416937629395121 66354432709812703222046341)
        ·
          refine ⟨12441456133089881854133689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66354432709812703222046341 12441456133089881854133689)
          ·
            refine ⟨9331092099817411390600267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12441456133089881854133689 9331092099817411390600267)
            ·
              refine ⟨13996638149726117085900401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9331092099817411390600267 13996638149726117085900401)
              ·
                refine ⟨10497478612294587814425301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13996638149726117085900401 10497478612294587814425301)
                ·
                  refine ⟨246034654975654401900593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10497478612294587814425301 246034654975654401900593)
                  ·
                    rfl

theorem cell23_4312357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 2, 7].length) (baseStart_4312357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312357 prefixEnd_4312357 := by exact prefixLift 4312357
  have htrace : WordTrace (prefixWord ++ tailWord_4312357) baseStart_4312357 baseEnd_4312357 := by
    simpa [prefixWord, tailWord_4312357, baseEnd_4312357] using wordTrace_append hprefix tailTrace_4312357
  have hstable : (prefixWord ++ tailWord_4312357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312357).length < 2 ^ (prefixWord ++ tailWord_4312357).sum := by decide
  have hdescent : baseEnd_4312357 < baseStart_4312357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312385 : List Nat := [1, 2, 5, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_4312385 : Nat := 118140960795 + 4312385 * 2 ^ 59
def prefixEnd_4312385 : Nat := 4983230072969 + 3 ^ 40 * 4312385 * 2
def baseEnd_4312385 : Nat := 2214326272239215507555209

theorem tailTrace_4312385 : CollatzResearch.WordTrace tailWord_4312385 prefixEnd_4312385 2214326272239215507555209 := by
  unfold tailWord_4312385
  simp only [CollatzResearch.WordTrace]
  refine ⟨157285602481973116567610609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104857068321315411045073739 157285602481973116567610609)
  ·
    refine ⟨117964201861479837425707957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157285602481973116567610609 117964201861479837425707957)
    ·
      refine ⟨11059143924513734758660121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 117964201861479837425707957 11059143924513734758660121)
      ·
        refine ⟨8294357943385301068995091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11059143924513734758660121 8294357943385301068995091)
        ·
          refine ⟨12441536915077951603492637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8294357943385301068995091 12441536915077951603492637)
          ·
            refine ⟨4665576343154231851309739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12441536915077951603492637 4665576343154231851309739)
            ·
              refine ⟨6998364514731347776964609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4665576343154231851309739 6998364514731347776964609)
              ·
                refine ⟨5248773386048510832723457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6998364514731347776964609 5248773386048510832723457)
                ·
                  refine ⟨3936580039536383124542593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5248773386048510832723457 3936580039536383124542593)
                  ·
                    refine ⟨2952435029652287343406945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3936580039536383124542593 2952435029652287343406945)
                    ·
                      refine ⟨2214326272239215507555209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2952435029652287343406945 2214326272239215507555209)
                      ·
                        rfl

theorem cell23_4312385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_4312385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312385 prefixEnd_4312385 := by exact prefixLift 4312385
  have htrace : WordTrace (prefixWord ++ tailWord_4312385) baseStart_4312385 baseEnd_4312385 := by
    simpa [prefixWord, tailWord_4312385, baseEnd_4312385] using wordTrace_append hprefix tailTrace_4312385
  have hstable : (prefixWord ++ tailWord_4312385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312385).length < 2 ^ (prefixWord ++ tailWord_4312385).sum := by decide
  have hdescent : baseEnd_4312385 < baseStart_4312385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312407 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 4]
def baseStart_4312407 : Nat := 118140960795 + 4312407 * 2 ^ 59
def prefixEnd_4312407 : Nat := 4983230072969 + 3 ^ 40 * 4312407 * 2
def baseEnd_4312407 : Nat := 2214337568813614421480107

theorem tailTrace_4312407 : CollatzResearch.WordTrace tailWord_4312407 prefixEnd_4312407 2214337568813614421480107 := by
  unfold tailWord_4312407
  simp only [CollatzResearch.WordTrace]
  refine ⟨157286404887893414324911475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104857603258595609549940983 157286404887893414324911475)
  ·
    refine ⟨235929607331840121487367213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157286404887893414324911475 235929607331840121487367213)
    ·
      refine ⟨88473602749440045557762705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235929607331840121487367213 88473602749440045557762705)
      ·
        refine ⟨66355202062080034168322029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88473602749440045557762705 66355202062080034168322029)
        ·
          refine ⟨24883200773280012813120761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66355202062080034168322029 24883200773280012813120761)
          ·
            refine ⟨18662400579960009609840571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24883200773280012813120761 18662400579960009609840571)
            ·
              refine ⟨27993600869940014414760857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18662400579960009609840571 27993600869940014414760857)
              ·
                refine ⟨20995200652455010811070643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27993600869940014414760857 20995200652455010811070643)
                ·
                  refine ⟨31492800978682516216605965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20995200652455010811070643 31492800978682516216605965)
                  ·
                    refine ⟨11809800367005943581227237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31492800978682516216605965 11809800367005943581227237)
                    ·
                      refine ⟨2214337568813614421480107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11809800367005943581227237 2214337568813614421480107)
                      ·
                        rfl

theorem cell23_4312407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_4312407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312407 prefixEnd_4312407 := by exact prefixLift 4312407
  have htrace : WordTrace (prefixWord ++ tailWord_4312407) baseStart_4312407 baseEnd_4312407 := by
    simpa [prefixWord, tailWord_4312407, baseEnd_4312407] using wordTrace_append hprefix tailTrace_4312407
  have hstable : (prefixWord ++ tailWord_4312407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312407).length < 2 ^ (prefixWord ++ tailWord_4312407).sum := by decide
  have hdescent : baseEnd_4312407 < baseStart_4312407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312444 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 2, 2, 3]
def baseStart_4312444 : Nat := 118140960795 + 4312444 * 2 ^ 59
def prefixEnd_4312444 : Nat := 4983230072969 + 3 ^ 40 * 4312444 * 2
def baseEnd_4312444 : Nat := 2214356567597830776717437

theorem tailTrace_4312444 : CollatzResearch.WordTrace tailWord_4312444 prefixEnd_4312444 2214356567597830776717437 := by
  unfold tailWord_4312444
  simp only [CollatzResearch.WordTrace]
  refine ⟨78643877194379684822004193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104858502925839579762672257 78643877194379684822004193)
  ·
    refine ⟨58982907895784763616503145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78643877194379684822004193 58982907895784763616503145)
    ·
      refine ⟨44237180921838572712377359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58982907895784763616503145 44237180921838572712377359)
      ·
        refine ⟨66355771382757859068566039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44237180921838572712377359 66355771382757859068566039)
        ·
          refine ⟨99533657074136788602849059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66355771382757859068566039 99533657074136788602849059)
          ·
            refine ⟨149300485611205182904273589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99533657074136788602849059 149300485611205182904273589)
            ·
              refine ⟨13996920526050485897275649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 149300485611205182904273589 13996920526050485897275649)
              ·
                refine ⟨10497690394537864422956737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13996920526050485897275649 10497690394537864422956737)
                ·
                  refine ⟨7873267795903398317217553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10497690394537864422956737 7873267795903398317217553)
                  ·
                    refine ⟨5904950846927548737913165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7873267795903398317217553 5904950846927548737913165)
                    ·
                      refine ⟨2214356567597830776717437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5904950846927548737913165 2214356567597830776717437)
                      ·
                        rfl

theorem cell23_4312444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_4312444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312444 prefixEnd_4312444 := by exact prefixLift 4312444
  have htrace : WordTrace (prefixWord ++ tailWord_4312444) baseStart_4312444 baseEnd_4312444 := by
    simpa [prefixWord, tailWord_4312444, baseEnd_4312444] using wordTrace_append hprefix tailTrace_4312444
  have hstable : (prefixWord ++ tailWord_4312444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312444).length < 2 ^ (prefixWord ++ tailWord_4312444).sum := by decide
  have hdescent : baseEnd_4312444 < baseStart_4312444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312451 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 3, 4]
def baseStart_4312451 : Nat := 118140960795 + 4312451 * 2 ^ 59
def prefixEnd_4312451 : Nat := 4983230072969 + 3 ^ 40 * 4312451 * 2
def baseEnd_4312451 : Nat := 738120053987470749776635

theorem tailTrace_4312451 : CollatzResearch.WordTrace tailWord_4312451 prefixEnd_4312451 738120053987470749776635 := by
  unfold tailWord_4312451
  simp only [CollatzResearch.WordTrace]
  refine ⟨157288009699734009839513207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104858673133156006559675471 157288009699734009839513207)
  ·
    refine ⟨235932014549601014759269811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157288009699734009839513207 235932014549601014759269811)
    ·
      refine ⟨353898021824401522138904717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235932014549601014759269811 353898021824401522138904717)
      ·
        refine ⟨132711758184150570802089269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 353898021824401522138904717 132711758184150570802089269)
        ·
          refine ⟨12441727329764116012695869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132711758184150570802089269 12441727329764116012695869)
          ·
            refine ⟨4665647748661543504760951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12441727329764116012695869 4665647748661543504760951)
            ·
              refine ⟨6998471622992315257141427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4665647748661543504760951 6998471622992315257141427)
              ·
                refine ⟨10497707434488472885712141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6998471622992315257141427 10497707434488472885712141)
                ·
                  refine ⟨3936640287933177332142053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10497707434488472885712141 3936640287933177332142053)
                  ·
                    refine ⟨738120053987470749776635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3936640287933177332142053 738120053987470749776635)
                    ·
                      rfl

theorem cell23_4312451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 4].length) (baseStart_4312451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312451 prefixEnd_4312451 := by exact prefixLift 4312451
  have htrace : WordTrace (prefixWord ++ tailWord_4312451) baseStart_4312451 baseEnd_4312451 := by
    simpa [prefixWord, tailWord_4312451, baseEnd_4312451] using wordTrace_append hprefix tailTrace_4312451
  have hstable : (prefixWord ++ tailWord_4312451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312451).length < 2 ^ (prefixWord ++ tailWord_4312451).sum := by decide
  have hdescent : baseEnd_4312451 < baseStart_4312451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312524 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 1, 6]
def baseStart_4312524 : Nat := 118140960795 + 4312524 * 2 ^ 59
def prefixEnd_4312524 : Nat := 4983230072969 + 3 ^ 40 * 4312524 * 2
def baseEnd_4312524 : Nat := 738132548683396821239023

theorem tailTrace_4312524 : CollatzResearch.WordTrace tailWord_4312524 prefixEnd_4312524 738132548683396821239023 := by
  unfold tailWord_4312524
  simp only [CollatzResearch.WordTrace]
  refine ⟨78645336114234771653460313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104860448152313028871280417 78645336114234771653460313)
  ·
    refine ⟨58984002085676078740095235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78645336114234771653460313 58984002085676078740095235)
    ·
      refine ⟨88476003128514118110142853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58984002085676078740095235 88476003128514118110142853)
      ·
        refine ⟨16589250586596397145651785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88476003128514118110142853 16589250586596397145651785)
        ·
          refine ⟨12441937939947297859238839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16589250586596397145651785 12441937939947297859238839)
          ·
            refine ⟨18662906909920946788858259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12441937939947297859238839 18662906909920946788858259)
            ·
              refine ⟨27994360364881420183287389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18662906909920946788858259 27994360364881420183287389)
              ·
                refine ⟨10497885136830532568732771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27994360364881420183287389 10497885136830532568732771)
                ·
                  refine ⟨15746827705245798853099157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10497885136830532568732771 15746827705245798853099157)
                  ·
                    refine ⟨738132548683396821239023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15746827705245798853099157 738132548683396821239023)
                    ·
                      rfl

theorem cell23_4312524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_4312524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312524 prefixEnd_4312524 := by exact prefixLift 4312524
  have htrace : WordTrace (prefixWord ++ tailWord_4312524) baseStart_4312524 baseEnd_4312524 := by
    simpa [prefixWord, tailWord_4312524, baseEnd_4312524] using wordTrace_append hprefix tailTrace_4312524
  have hstable : (prefixWord ++ tailWord_4312524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312524).length < 2 ^ (prefixWord ++ tailWord_4312524).sum := by decide
  have hdescent : baseEnd_4312524 < baseStart_4312524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312527 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 6]
def baseStart_4312527 : Nat := 118140960795 + 4312527 * 2 ^ 59
def prefixEnd_4312527 : Nat := 4983230072969 + 3 ^ 40 * 4312527 * 2
def baseEnd_4312527 : Nat := 2214399186492153951979555

theorem tailTrace_4312527 : CollatzResearch.WordTrace tailWord_4312527 prefixEnd_4312527 2214399186492153951979555 := by
  unfold tailWord_4312527
  simp only [CollatzResearch.WordTrace]
  refine ⟨157290781647458674819279835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104860521098305783212853223 157290781647458674819279835)
  ·
    refine ⟨235936172471188012228919753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157290781647458674819279835 235936172471188012228919753)
    ·
      refine ⟨176952129353391009171689815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235936172471188012228919753 176952129353391009171689815)
      ·
        refine ⟨265428194030086513757534723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176952129353391009171689815 265428194030086513757534723)
        ·
          refine ⟨398142291045129770636302085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265428194030086513757534723 398142291045129770636302085)
          ·
            refine ⟨74651679570961831994306641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 398142291045129770636302085 74651679570961831994306641)
            ·
              refine ⟨55988759678221373995729981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74651679570961831994306641 55988759678221373995729981)
              ·
                refine ⟨20995784879333015248398743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 55988759678221373995729981 20995784879333015248398743)
                ·
                  refine ⟨31493677318999522872598115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20995784879333015248398743 31493677318999522872598115)
                  ·
                    refine ⟨47240515978499284308897173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31493677318999522872598115 47240515978499284308897173)
                    ·
                      refine ⟨2214399186492153951979555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47240515978499284308897173 2214399186492153951979555)
                      ·
                        rfl

theorem cell23_4312527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_4312527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312527 prefixEnd_4312527 := by exact prefixLift 4312527
  have htrace : WordTrace (prefixWord ++ tailWord_4312527) baseStart_4312527 baseEnd_4312527 := by
    simpa [prefixWord, tailWord_4312527, baseEnd_4312527] using wordTrace_append hprefix tailTrace_4312527
  have hstable : (prefixWord ++ tailWord_4312527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312527).length < 2 ^ (prefixWord ++ tailWord_4312527).sum := by decide
  have hdescent : baseEnd_4312527 < baseStart_4312527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312554 : List Nat := [3, 1, 3, 1, 4, 1, 10]
def baseStart_4312554 : Nat := 118140960795 + 4312554 * 2 ^ 59
def prefixEnd_4312554 : Nat := 4983230072969 + 3 ^ 40 * 4312554 * 2
def baseEnd_4312554 : Nat := 27338432721849695633851

theorem tailTrace_4312554 : CollatzResearch.WordTrace tailWord_4312554 prefixEnd_4312554 27338432721849695633851 := by
  unfold tailWord_4312554
  simp only [CollatzResearch.WordTrace]
  refine ⟨39322941604590214607628179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104861177612240572287008477 39322941604590214607628179)
  ·
    refine ⟨58984412406885321911442269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39322941604590214607628179 58984412406885321911442269)
    ·
      refine ⟨22119154652581995716790851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58984412406885321911442269 22119154652581995716790851)
      ·
        refine ⟨33178731978872993575186277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22119154652581995716790851 33178731978872993575186277)
        ·
          refine ⟨6221012246038686295347427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33178731978872993575186277 6221012246038686295347427)
          ·
            refine ⟨9331518369058029443021141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6221012246038686295347427 9331518369058029443021141)
            ·
              refine ⟨27338432721849695633851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9331518369058029443021141 27338432721849695633851)
              ·
                rfl

theorem cell23_4312554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 10].length) (baseStart_4312554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312554 prefixEnd_4312554 := by exact prefixLift 4312554
  have htrace : WordTrace (prefixWord ++ tailWord_4312554) baseStart_4312554 baseEnd_4312554 := by
    simpa [prefixWord, tailWord_4312554, baseEnd_4312554] using wordTrace_append hprefix tailTrace_4312554
  have hstable : (prefixWord ++ tailWord_4312554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312554).length < 2 ^ (prefixWord ++ tailWord_4312554).sum := by decide
  have hdescent : baseEnd_4312554 < baseStart_4312554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312565 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_4312565 : Nat := 118140960795 + 4312565 * 2 ^ 59
def prefixEnd_4312565 : Nat := 4983230072969 + 3 ^ 40 * 4312565 * 2
def baseEnd_4312565 : Nat := 2214418698757024803304381

theorem tailTrace_4312565 : CollatzResearch.WordTrace tailWord_4312565 prefixEnd_4312565 2214418698757024803304381 := by
  unfold tailWord_4312565
  simp only [CollatzResearch.WordTrace]
  refine ⟨157292167621321007309163149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104861445080880671539442099 157292167621321007309163149)
  ·
    refine ⟨58984562857995377740936181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157292167621321007309163149 58984562857995377740936181)
    ·
      refine ⟨5529802767937066663212767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 58984562857995377740936181 5529802767937066663212767)
      ·
        refine ⟨8294704151905599994819151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5529802767937066663212767 8294704151905599994819151)
        ·
          refine ⟨12442056227858399992228727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8294704151905599994819151 12442056227858399992228727)
          ·
            refine ⟨18663084341787599988343091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12442056227858399992228727 18663084341787599988343091)
            ·
              refine ⟨27994626512681399982514637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18663084341787599988343091 27994626512681399982514637)
              ·
                refine ⟨10497984942255524993442989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27994626512681399982514637 10497984942255524993442989)
                ·
                  refine ⟨3936744353345821872541121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10497984942255524993442989 3936744353345821872541121)
                  ·
                    refine ⟨2952558265009366404405841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3936744353345821872541121 2952558265009366404405841)
                    ·
                      refine ⟨2214418698757024803304381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2952558265009366404405841 2214418698757024803304381)
                      ·
                        rfl

theorem cell23_4312565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_4312565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312565 prefixEnd_4312565 := by exact prefixLift 4312565
  have htrace : WordTrace (prefixWord ++ tailWord_4312565) baseStart_4312565 baseEnd_4312565 := by
    simpa [prefixWord, tailWord_4312565, baseEnd_4312565] using wordTrace_append hprefix tailTrace_4312565
  have hstable : (prefixWord ++ tailWord_4312565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312565).length < 2 ^ (prefixWord ++ tailWord_4312565).sum := by decide
  have hdescent : baseEnd_4312565 < baseStart_4312565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312567 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 2, 7]
def baseStart_4312567 : Nat := 118140960795 + 4312567 * 2 ^ 59
def prefixEnd_4312567 : Nat := 4983230072969 + 3 ^ 40 * 4312567 * 2
def baseEnd_4312567 : Nat := 738139908572777931826457

theorem tailTrace_4312567 : CollatzResearch.WordTrace tailWord_4312567 prefixEnd_4312567 738139908572777931826457 := by
  unfold tailWord_4312567
  simp only [CollatzResearch.WordTrace]
  refine ⟨157292240567313761650735955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104861493711542507767157303 157292240567313761650735955)
  ·
    refine ⟨235938360850970642476103933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157292240567313761650735955 235938360850970642476103933)
    ·
      refine ⟨88476885319113990928538975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235938360850970642476103933 88476885319113990928538975)
      ·
        refine ⟨132715327978670986392808463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88476885319113990928538975 132715327978670986392808463)
        ·
          refine ⟨199072991968006479589212695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132715327978670986392808463 199072991968006479589212695)
          ·
            refine ⟨298609487952009719383819043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199072991968006479589212695 298609487952009719383819043)
            ·
              refine ⟨447914231928014579075728565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298609487952009719383819043 447914231928014579075728565)
              ·
                refine ⟨41991959243251366788349553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 447914231928014579075728565 41991959243251366788349553)
                ·
                  refine ⟨31493969432438525091262165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41991959243251366788349553 31493969432438525091262165)
                  ·
                    refine ⟨738139908572777931826457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31493969432438525091262165 738139908572777931826457)
                    ·
                      rfl

theorem cell23_4312567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_4312567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312567 prefixEnd_4312567 := by exact prefixLift 4312567
  have htrace : WordTrace (prefixWord ++ tailWord_4312567) baseStart_4312567 baseEnd_4312567 := by
    simpa [prefixWord, tailWord_4312567, baseEnd_4312567] using wordTrace_append hprefix tailTrace_4312567
  have hstable : (prefixWord ++ tailWord_4312567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312567).length < 2 ^ (prefixWord ++ tailWord_4312567).sum := by decide
  have hdescent : baseEnd_4312567 < baseStart_4312567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312578 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 1, 2, 4]
def baseStart_4312578 : Nat := 118140960795 + 4312578 * 2 ^ 59
def prefixEnd_4312578 : Nat := 4983230072969 + 3 ^ 40 * 4312578 * 2
def baseEnd_4312578 : Nat := 2214425374005533252441821

theorem tailTrace_4312578 : CollatzResearch.WordTrace tailWord_4312578 prefixEnd_4312578 2214425374005533252441821 := by
  unfold tailWord_4312578
  simp only [CollatzResearch.WordTrace]
  refine ⟨39323160442568477632346597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104861761180182607019590925 39323160442568477632346597)
  ·
    refine ⟨7373092582981589556064987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39323160442568477632346597 7373092582981589556064987)
    ·
      refine ⟨11059638874472384334097481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7373092582981589556064987 11059638874472384334097481)
      ·
        refine ⟨8294729155854288250573111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11059638874472384334097481 8294729155854288250573111)
        ·
          refine ⟨12442093733781432375859667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8294729155854288250573111 12442093733781432375859667)
          ·
            refine ⟨18663140600672148563789501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12442093733781432375859667 18663140600672148563789501)
            ·
              refine ⟨6998677725252055711421063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18663140600672148563789501 6998677725252055711421063)
              ·
                refine ⟨10498016587878083567131595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6998677725252055711421063 10498016587878083567131595)
                ·
                  refine ⟨15747024881817125350697393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10498016587878083567131595 15747024881817125350697393)
                  ·
                    refine ⟨11810268661362844013023045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15747024881817125350697393 11810268661362844013023045)
                    ·
                      refine ⟨2214425374005533252441821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11810268661362844013023045 2214425374005533252441821)
                      ·
                        rfl

theorem cell23_4312578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_4312578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312578 prefixEnd_4312578 := by exact prefixLift 4312578
  have htrace : WordTrace (prefixWord ++ tailWord_4312578) baseStart_4312578 baseEnd_4312578 := by
    simpa [prefixWord, tailWord_4312578, baseEnd_4312578] using wordTrace_append hprefix tailTrace_4312578
  have hstable : (prefixWord ++ tailWord_4312578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312578).length < 2 ^ (prefixWord ++ tailWord_4312578).sum := by decide
  have hdescent : baseEnd_4312578 < baseStart_4312578 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312588 : List Nat := [2, 2, 1, 2, 6, 1, 2, 7]
def baseStart_4312588 : Nat := 118140960795 + 4312588 * 2 ^ 59
def prefixEnd_4312588 : Nat := 4983230072969 + 3 ^ 40 * 4312588 * 2
def baseEnd_4312588 : Nat := 82015944770817711604325

theorem tailTrace_4312588 : CollatzResearch.WordTrace tailWord_4312588 prefixEnd_4312588 82015944770817711604325 := by
  unfold tailWord_4312588
  simp only [CollatzResearch.WordTrace]
  refine ⟨78646503250118841118625209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104862004333491788158166945 78646503250118841118625209)
  ·
    refine ⟨58984877437589130838968907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78646503250118841118625209 58984877437589130838968907)
    ·
      refine ⟨88477316156383696258453361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58984877437589130838968907 88477316156383696258453361)
      ·
        refine ⟨66357987117287772193840021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88477316156383696258453361 66357987117287772193840021)
        ·
          refine ⟨3110530646122864321586251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66357987117287772193840021 3110530646122864321586251)
          ·
            refine ⟨4665795969184296482379377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3110530646122864321586251 4665795969184296482379377)
            ·
              refine ⟨3499346976888222361784533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4665795969184296482379377 3499346976888222361784533)
              ·
                refine ⟨82015944770817711604325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3499346976888222361784533 82015944770817711604325)
                ·
                  rfl

theorem cell23_4312588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 7].length) (baseStart_4312588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312588 prefixEnd_4312588 := by exact prefixLift 4312588
  have htrace : WordTrace (prefixWord ++ tailWord_4312588) baseStart_4312588 baseEnd_4312588 := by
    simpa [prefixWord, tailWord_4312588, baseEnd_4312588] using wordTrace_append hprefix tailTrace_4312588
  have hstable : (prefixWord ++ tailWord_4312588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312588).length < 2 ^ (prefixWord ++ tailWord_4312588).sum := by decide
  have hdescent : baseEnd_4312588 < baseStart_4312588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312624 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 3]
def baseStart_4312624 : Nat := 118140960795 + 4312624 * 2 ^ 59
def prefixEnd_4312624 : Nat := 4983230072969 + 3 ^ 40 * 4312624 * 2
def baseEnd_4312624 : Nat := 2214448994115640072466609

theorem tailTrace_4312624 : CollatzResearch.WordTrace tailWord_4312624 prefixEnd_4312624 2214448994115640072466609 := by
  unfold tailWord_4312624
  simp only [CollatzResearch.WordTrace]
  refine ⟨78647159764053630192780463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104862879685404840257040617 78647159764053630192780463)
  ·
    refine ⟨117970739646080445289170695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78647159764053630192780463 117970739646080445289170695)
    ·
      refine ⟨176956109469120667933756043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117970739646080445289170695 176956109469120667933756043)
      ·
        refine ⟨265434164203681001900634065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176956109469120667933756043 265434164203681001900634065)
        ·
          refine ⟨199075623152760751425475549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265434164203681001900634065 199075623152760751425475549)
          ·
            refine ⟨74653358682285281784553331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199075623152760751425475549 74653358682285281784553331)
            ·
              refine ⟨111980038023427922676829997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74653358682285281784553331 111980038023427922676829997)
              ·
                refine ⟨41992514258785471003811249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 111980038023427922676829997 41992514258785471003811249)
                ·
                  refine ⟨31494385694089103252858437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41992514258785471003811249 31494385694089103252858437)
                  ·
                    refine ⟨5905197317641706859910957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31494385694089103252858437 5905197317641706859910957)
                    ·
                      refine ⟨2214448994115640072466609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5905197317641706859910957 2214448994115640072466609)
                      ·
                        rfl

theorem cell23_4312624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 3].length) (baseStart_4312624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312624 prefixEnd_4312624 := by exact prefixLift 4312624
  have htrace : WordTrace (prefixWord ++ tailWord_4312624) baseStart_4312624 baseEnd_4312624 := by
    simpa [prefixWord, tailWord_4312624, baseEnd_4312624] using wordTrace_append hprefix tailTrace_4312624
  have hstable : (prefixWord ++ tailWord_4312624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312624).length < 2 ^ (prefixWord ++ tailWord_4312624).sum := by decide
  have hdescent : baseEnd_4312624 < baseStart_4312624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312634 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4]
def baseStart_4312634 : Nat := 118140960795 + 4312634 * 2 ^ 59
def prefixEnd_4312634 : Nat := 4983230072969 + 3 ^ 40 * 4312634 * 2
def baseEnd_4312634 : Nat := 2214454128922185033341563

theorem tailTrace_4312634 : CollatzResearch.WordTrace tailWord_4312634 prefixEnd_4312634 2214454128922185033341563 := by
  unfold tailWord_4312634
  simp only [CollatzResearch.WordTrace]
  refine ⟨39323671064517758023356239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104863122838714021395616637 39323671064517758023356239)
  ·
    refine ⟨58985506596776637035034359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39323671064517758023356239 58985506596776637035034359)
    ·
      refine ⟨88478259895164955552551539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58985506596776637035034359 88478259895164955552551539)
      ·
        refine ⟨132717389842747433328827309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88478259895164955552551539 132717389842747433328827309)
        ·
          refine ⟨49769021191030287498310241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132717389842747433328827309 49769021191030287498310241)
          ·
            refine ⟨37326765893272715623732681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49769021191030287498310241 37326765893272715623732681)
            ·
              refine ⟨27995074419954536717799511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37326765893272715623732681 27995074419954536717799511)
              ·
                refine ⟨41992611629931805076699267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27995074419954536717799511 41992611629931805076699267)
                ·
                  refine ⟨62988917444897707615048901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41992611629931805076699267 62988917444897707615048901)
                  ·
                    refine ⟨11810422020918320177821669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62988917444897707615048901 11810422020918320177821669)
                    ·
                      refine ⟨2214454128922185033341563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11810422020918320177821669 2214454128922185033341563)
                      ·
                        rfl

theorem cell23_4312634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_4312634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312634 prefixEnd_4312634 := by exact prefixLift 4312634
  have htrace : WordTrace (prefixWord ++ tailWord_4312634) baseStart_4312634 baseEnd_4312634 := by
    simpa [prefixWord, tailWord_4312634, baseEnd_4312634] using wordTrace_append hprefix tailTrace_4312634
  have hstable : (prefixWord ++ tailWord_4312634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312634).length < 2 ^ (prefixWord ++ tailWord_4312634).sum := by decide
  have hdescent : baseEnd_4312634 < baseStart_4312634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312661 : List Nat := [1, 3, 2, 2, 1, 1, 1, 7, 5]
def baseStart_4312661 : Nat := 118140960795 + 4312661 * 2 ^ 59
def prefixEnd_4312661 : Nat := 4983230072969 + 3 ^ 40 * 4312661 * 2
def baseEnd_4312661 : Nat := 246051999211095158633771

theorem tailTrace_4312661 : CollatzResearch.WordTrace tailWord_4312661 prefixEnd_4312661 246051999211095158633771 := by
  unfold tailWord_4312661
  simp only [CollatzResearch.WordTrace]
  refine ⟨157295669028973215704657837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104863779352648810469771891 157295669028973215704657837)
  ·
    refine ⟨58985875885864955889246689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157295669028973215704657837 58985875885864955889246689)
    ·
      refine ⟨44239406914398716916935017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 58985875885864955889246689 44239406914398716916935017)
      ·
        refine ⟨33179555185799037687701263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44239406914398716916935017 33179555185799037687701263)
        ·
          refine ⟨49769332778698556531551895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33179555185799037687701263 49769332778698556531551895)
          ·
            refine ⟨74653999168047834797327843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49769332778698556531551895 74653999168047834797327843)
            ·
              refine ⟨111980998752071752195991765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74653999168047834797327843 111980998752071752195991765)
              ·
                refine ⟨2624554658251681692093557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 111980998752071752195991765 2624554658251681692093557)
                ·
                  refine ⟨246051999211095158633771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2624554658251681692093557 246051999211095158633771)
                  ·
                    rfl

theorem cell23_4312661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 5].length) (baseStart_4312661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312661 prefixEnd_4312661 := by exact prefixLift 4312661
  have htrace : WordTrace (prefixWord ++ tailWord_4312661) baseStart_4312661 baseEnd_4312661 := by
    simpa [prefixWord, tailWord_4312661, baseEnd_4312661] using wordTrace_append hprefix tailTrace_4312661
  have hstable : (prefixWord ++ tailWord_4312661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312661).length < 2 ^ (prefixWord ++ tailWord_4312661).sum := by decide
  have hdescent : baseEnd_4312661 < baseStart_4312661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312681 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 2, 5, 2]
def baseStart_4312681 : Nat := 118140960795 + 4312681 * 2 ^ 59
def prefixEnd_4312681 : Nat := 4983230072969 + 3 ^ 40 * 4312681 * 2
def baseEnd_4312681 : Nat := 2214478262512946349453847

theorem tailTrace_4312681 : CollatzResearch.WordTrace tailWord_4312681 prefixEnd_4312681 2214478262512946349453847 := by
  unfold tailWord_4312681
  simp only [CollatzResearch.WordTrace]
  refine ⟨157296398488900759120385897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104864265659267172746923931 157296398488900759120385897)
  ·
    refine ⟨117972298866675569340289423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157296398488900759120385897 117972298866675569340289423)
    ·
      refine ⟨176958448300013354010434135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117972298866675569340289423 176958448300013354010434135)
      ·
        refine ⟨265437672450020031015651203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176958448300013354010434135 265437672450020031015651203)
        ·
          refine ⟨398156508675030046523476805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265437672450020031015651203 398156508675030046523476805)
          ·
            refine ⟨74654345376568133723151901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 398156508675030046523476805 74654345376568133723151901)
            ·
              refine ⟨27995379516213050146181963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74654345376568133723151901 27995379516213050146181963)
              ·
                refine ⟨41993069274319575219272945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27995379516213050146181963 41993069274319575219272945)
                ·
                  refine ⟨31494801955739681414454709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 41993069274319575219272945 31494801955739681414454709)
                  ·
                    refine ⟨2952637683350595132605129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31494801955739681414454709 2952637683350595132605129)
                    ·
                      refine ⟨2214478262512946349453847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2952637683350595132605129 2214478262512946349453847)
                      ·
                        rfl

theorem cell23_4312681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 5, 2].length) (baseStart_4312681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312681 prefixEnd_4312681 := by exact prefixLift 4312681
  have htrace : WordTrace (prefixWord ++ tailWord_4312681) baseStart_4312681 baseEnd_4312681 := by
    simpa [prefixWord, tailWord_4312681, baseEnd_4312681] using wordTrace_append hprefix tailTrace_4312681
  have hstable : (prefixWord ++ tailWord_4312681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312681).length < 2 ^ (prefixWord ++ tailWord_4312681).sum := by decide
  have hdescent : baseEnd_4312681 < baseStart_4312681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312711 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_4312711 : Nat := 118140960795 + 4312711 * 2 ^ 59
def prefixEnd_4312711 : Nat := 4983230072969 + 3 ^ 40 * 4312711 * 2
def baseEnd_4312711 : Nat := 2214493666932581232078709

theorem tailTrace_4312711 : CollatzResearch.WordTrace tailWord_4312711 prefixEnd_4312711 2214493666932581232078709 := by
  unfold tailWord_4312711
  simp only [CollatzResearch.WordTrace]
  refine ⟨157297492678792074243977987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104864995119194716162651991 157297492678792074243977987)
  ·
    refine ⟨235946239018188111365966981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157297492678792074243977987 235946239018188111365966981)
    ·
      refine ⟨44239919815910270881118809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 235946239018188111365966981 44239919815910270881118809)
      ·
        refine ⟨33179939861932703160839107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44239919815910270881118809 33179939861932703160839107)
        ·
          refine ⟨49769909792899054741258661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33179939861932703160839107 49769909792899054741258661)
          ·
            refine ⟨9331858086168572763985999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49769909792899054741258661 9331858086168572763985999)
            ·
              refine ⟨13997787129252859145978999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9331858086168572763985999 13997787129252859145978999)
              ·
                refine ⟨20996680693879288718968499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13997787129252859145978999 20996680693879288718968499)
                ·
                  refine ⟨31495021040818933078452749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20996680693879288718968499 31495021040818933078452749)
                  ·
                    refine ⟨11810632890307099904419781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31495021040818933078452749 11810632890307099904419781)
                    ·
                      refine ⟨2214493666932581232078709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11810632890307099904419781 2214493666932581232078709)
                      ·
                        rfl

theorem cell23_4312711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_4312711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312711 prefixEnd_4312711 := by exact prefixLift 4312711
  have htrace : WordTrace (prefixWord ++ tailWord_4312711) baseStart_4312711 baseEnd_4312711 := by
    simpa [prefixWord, tailWord_4312711, baseEnd_4312711] using wordTrace_append hprefix tailTrace_4312711
  have hstable : (prefixWord ++ tailWord_4312711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312711).length < 2 ^ (prefixWord ++ tailWord_4312711).sum := by decide
  have hdescent : baseEnd_4312711 < baseStart_4312711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312728 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 2, 4, 2]
def baseStart_4312728 : Nat := 118140960795 + 4312728 * 2 ^ 59
def prefixEnd_4312728 : Nat := 4983230072969 + 3 ^ 40 * 4312728 * 2
def baseEnd_4312728 : Nat := 2214502396103707665566131

theorem tailTrace_4312728 : CollatzResearch.WordTrace tailWord_4312728 prefixEnd_4312728 2214502396103707665566131 := by
  unfold tailWord_4312728
  simp only [CollatzResearch.WordTrace]
  refine ⟨78649056359865243073673419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104865408479820324098231225 78649056359865243073673419)
  ·
    refine ⟨117973584539797864610510129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78649056359865243073673419 117973584539797864610510129)
    ·
      refine ⟨88480188404848398457882597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117973584539797864610510129 88480188404848398457882597)
      ·
        refine ⟨16590035325909074710852987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88480188404848398457882597 16590035325909074710852987)
        ·
          refine ⟨24885052988863612066279481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16590035325909074710852987 24885052988863612066279481)
          ·
            refine ⟨18663789741647709049709611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24885052988863612066279481 18663789741647709049709611)
            ·
              refine ⟨27995684612471563574564417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18663789741647709049709611 27995684612471563574564417)
              ·
                refine ⟨20996763459353672680923313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27995684612471563574564417 20996763459353672680923313)
                ·
                  refine ⟨15747572594515254510692485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20996763459353672680923313 15747572594515254510692485)
                  ·
                    refine ⟨2952669861471610220754841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15747572594515254510692485 2952669861471610220754841)
                    ·
                      refine ⟨2214502396103707665566131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2952669861471610220754841 2214502396103707665566131)
                      ·
                        rfl

theorem cell23_4312728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_4312728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312728 prefixEnd_4312728 := by exact prefixLift 4312728
  have htrace : WordTrace (prefixWord ++ tailWord_4312728) baseStart_4312728 baseEnd_4312728 := by
    simpa [prefixWord, tailWord_4312728, baseEnd_4312728] using wordTrace_append hprefix tailTrace_4312728
  have hstable : (prefixWord ++ tailWord_4312728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312728).length < 2 ^ (prefixWord ++ tailWord_4312728).sum := by decide
  have hdescent : baseEnd_4312728 < baseStart_4312728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312818 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_4312818 : Nat := 118140960795 + 4312818 * 2 ^ 59
def prefixEnd_4312818 : Nat := 4983230072969 + 3 ^ 40 * 4312818 * 2
def baseEnd_4312818 : Nat := 2214548609362612313440717

theorem tailTrace_4312818 : CollatzResearch.WordTrace tailWord_4312818 prefixEnd_4312818 2214548609362612313440717 := by
  unfold tailWord_4312818
  simp only [CollatzResearch.WordTrace]
  refine ⟨39325348822351107879530777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104867596859602954345415405 39325348822351107879530777)
  ·
    refine ⟨29494011616763330909648083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39325348822351107879530777 29494011616763330909648083)
    ·
      refine ⟨44241017425144996364472125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29494011616763330909648083 44241017425144996364472125)
      ·
        refine ⟨16590381534429373636677047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44241017425144996364472125 16590381534429373636677047)
        ·
          refine ⟨24885572301644060455015571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16590381534429373636677047 24885572301644060455015571)
          ·
            refine ⟨37328358452466090682523357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24885572301644060455015571 37328358452466090682523357)
            ·
              refine ⟨13998134419674784005946259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37328358452466090682523357 13998134419674784005946259)
              ·
                refine ⟨20997201629512176008919389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13998134419674784005946259 20997201629512176008919389)
                ·
                  refine ⟨7873950611067066003344771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20997201629512176008919389 7873950611067066003344771)
                  ·
                    refine ⟨11810925916600599005017157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7873950611067066003344771 11810925916600599005017157)
                    ·
                      refine ⟨2214548609362612313440717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11810925916600599005017157 2214548609362612313440717)
                      ·
                        rfl

theorem cell23_4312818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_4312818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312818 prefixEnd_4312818 := by exact prefixLift 4312818
  have htrace : WordTrace (prefixWord ++ tailWord_4312818) baseStart_4312818 baseEnd_4312818 := by
    simpa [prefixWord, tailWord_4312818, baseEnd_4312818] using wordTrace_append hprefix tailTrace_4312818
  have hstable : (prefixWord ++ tailWord_4312818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312818).length < 2 ^ (prefixWord ++ tailWord_4312818).sum := by decide
  have hdescent : baseEnd_4312818 < baseStart_4312818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312822 : List Nat := [5, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2]
def baseStart_4312822 : Nat := 118140960795 + 4312822 * 2 ^ 59
def prefixEnd_4312822 : Nat := 4983230072969 + 3 ^ 40 * 4312822 * 2
def baseEnd_4312822 : Nat := 2214550663285230297790699

theorem tailTrace_4312822 : CollatzResearch.WordTrace tailWord_4312822 prefixEnd_4312822 2214550663285230297790699 := by
  unfold tailWord_4312822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9831346323836871262579295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104867694120926626800845813 9831346323836871262579295)
  ·
    refine ⟨14747019485755306893868943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9831346323836871262579295 14747019485755306893868943)
    ·
      refine ⟨22120529228632960340803415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14747019485755306893868943 22120529228632960340803415)
      ·
        refine ⟨33180793842949440511205123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22120529228632960340803415 33180793842949440511205123)
        ·
          refine ⟨49771190764424160766807685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33180793842949440511205123 49771190764424160766807685)
          ·
            refine ⟨9332098268329530143776441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49771190764424160766807685 9332098268329530143776441)
            ·
              refine ⟨6999073701247147607832331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9332098268329530143776441 6999073701247147607832331)
              ·
                refine ⟨10498610551870721411748497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6999073701247147607832331 10498610551870721411748497)
                ·
                  refine ⟨7873957913903041058811373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10498610551870721411748497 7873957913903041058811373)
                  ·
                    refine ⟨2952734217713640397054265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7873957913903041058811373 2952734217713640397054265)
                    ·
                      refine ⟨2214550663285230297790699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2952734217713640397054265 2214550663285230297790699)
                      ·
                        rfl

theorem cell23_4312822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_4312822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312822 prefixEnd_4312822 := by exact prefixLift 4312822
  have htrace : WordTrace (prefixWord ++ tailWord_4312822) baseStart_4312822 baseEnd_4312822 := by
    simpa [prefixWord, tailWord_4312822, baseEnd_4312822] using wordTrace_append hprefix tailTrace_4312822
  have hstable : (prefixWord ++ tailWord_4312822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312822).length < 2 ^ (prefixWord ++ tailWord_4312822).sum := by decide
  have hdescent : baseEnd_4312822 < baseStart_4312822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312831 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 4]
def baseStart_4312831 : Nat := 118140960795 + 4312831 * 2 ^ 59
def prefixEnd_4312831 : Nat := 4983230072969 + 3 ^ 40 * 4312831 * 2
def baseEnd_4312831 : Nat := 2214555284611120762578157

theorem tailTrace_4312831 : CollatzResearch.WordTrace tailWord_4312831 prefixEnd_4312831 2214555284611120762578157 := by
  unfold tailWord_4312831
  simp only [CollatzResearch.WordTrace]
  refine ⟨157301869438357334738346347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104867912958904889825564231 157301869438357334738346347)
  ·
    refine ⟨235952804157536002107519521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157301869438357334738346347 235952804157536002107519521)
    ·
      refine ⟨176964603118152001580639641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235952804157536002107519521 176964603118152001580639641)
      ·
        refine ⟨132723452338614001185479731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176964603118152001580639641 132723452338614001185479731)
        ·
          refine ⟨199085178507921001778219597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132723452338614001185479731 199085178507921001778219597)
          ·
            refine ⟨74656941940470375666832349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199085178507921001778219597 74656941940470375666832349)
            ·
              refine ⟨27996353227676390875062131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74656941940470375666832349 27996353227676390875062131)
              ·
                refine ⟨41994529841514586312593197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27996353227676390875062131 41994529841514586312593197)
                ·
                  refine ⟨15747948690567969867222449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41994529841514586312593197 15747948690567969867222449)
                  ·
                    refine ⟨11810961517925977400416837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15747948690567969867222449 11810961517925977400416837)
                    ·
                      refine ⟨2214555284611120762578157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11810961517925977400416837 2214555284611120762578157)
                      ·
                        rfl

theorem cell23_4312831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_4312831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312831 prefixEnd_4312831 := by exact prefixLift 4312831
  have htrace : WordTrace (prefixWord ++ tailWord_4312831) baseStart_4312831 baseEnd_4312831 := by
    simpa [prefixWord, tailWord_4312831, baseEnd_4312831] using wordTrace_append hprefix tailTrace_4312831
  have hstable : (prefixWord ++ tailWord_4312831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312831).length < 2 ^ (prefixWord ++ tailWord_4312831).sum := by decide
  have hdescent : baseEnd_4312831 < baseStart_4312831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312858 : List Nat := [3, 1, 1, 3, 2, 4, 1, 8]
def baseStart_4312858 : Nat := 118140960795 + 4312858 * 2 ^ 59
def prefixEnd_4312858 : Nat := 4983230072969 + 3 ^ 40 * 4312858 * 2
def baseEnd_4312858 : Nat := 82021079577362672479279

theorem tailTrace_4312858 : CollatzResearch.WordTrace tailWord_4312858 prefixEnd_4312858 82021079577362672479279 := by
  unfold tailWord_4312858
  simp only [CollatzResearch.WordTrace]
  refine ⟨39325713552314879587394807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104868569472839678899719485 39325713552314879587394807)
  ·
    refine ⟨58988570328472319381092211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39325713552314879587394807 58988570328472319381092211)
    ·
      refine ⟨88482855492708479071638317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58988570328472319381092211 88482855492708479071638317)
      ·
        refine ⟨33181070809765679651864369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88482855492708479071638317 33181070809765679651864369)
        ·
          refine ⟨24885803107324259738898277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33181070809765679651864369 24885803107324259738898277)
          ·
            refine ⟨4666088082623298701043427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24885803107324259738898277 4666088082623298701043427)
            ·
              refine ⟨6999132123934948051565141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4666088082623298701043427 6999132123934948051565141)
              ·
                refine ⟨82021079577362672479279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6999132123934948051565141 82021079577362672479279)
                ·
                  rfl

theorem cell23_4312858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 8].length) (baseStart_4312858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312858 prefixEnd_4312858 := by exact prefixLift 4312858
  have htrace : WordTrace (prefixWord ++ tailWord_4312858) baseStart_4312858 baseEnd_4312858 := by
    simpa [prefixWord, tailWord_4312858, baseEnd_4312858] using wordTrace_append hprefix tailTrace_4312858
  have hstable : (prefixWord ++ tailWord_4312858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312858).length < 2 ^ (prefixWord ++ tailWord_4312858).sum := by decide
  have hdescent : baseEnd_4312858 < baseStart_4312858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312886 : List Nat := [5, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2]
def baseStart_4312886 : Nat := 118140960795 + 4312886 * 2 ^ 59
def prefixEnd_4312886 : Nat := 4983230072969 + 3 ^ 40 * 4312886 * 2
def baseEnd_4312886 : Nat := 2214583526047118047390405

theorem tailTrace_4312886 : CollatzResearch.WordTrace tailWord_4312886 prefixEnd_4312886 2214583526047118047390405 := by
  unfold tailWord_4312886
  simp only [CollatzResearch.WordTrace]
  refine ⟨9831492215822379945724907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104869250302105386087732341 9831492215822379945724907)
  ·
    refine ⟨14747238323733569918587361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9831492215822379945724907 14747238323733569918587361)
    ·
      refine ⟨11060428742800177438940521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14747238323733569918587361 11060428742800177438940521)
      ·
        refine ⟨8295321557100133079205391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11060428742800177438940521 8295321557100133079205391)
        ·
          refine ⟨12442982335650199618808087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8295321557100133079205391 12442982335650199618808087)
          ·
            refine ⟨18664473503475299428212131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12442982335650199618808087 18664473503475299428212131)
            ·
              refine ⟨27996710255212949142318197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18664473503475299428212131 27996710255212949142318197)
              ·
                refine ⟨2624691586426213982092331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27996710255212949142318197 2624691586426213982092331)
                ·
                  refine ⟨3937037379639320973138497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2624691586426213982092331 3937037379639320973138497)
                  ·
                    refine ⟨2952778034729490729853873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3937037379639320973138497 2952778034729490729853873)
                    ·
                      refine ⟨2214583526047118047390405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2952778034729490729853873 2214583526047118047390405)
                      ·
                        rfl

theorem cell23_4312886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_4312886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312886 prefixEnd_4312886 := by exact prefixLift 4312886
  have htrace : WordTrace (prefixWord ++ tailWord_4312886) baseStart_4312886 baseEnd_4312886 := by
    simpa [prefixWord, tailWord_4312886, baseEnd_4312886] using wordTrace_append hprefix tailTrace_4312886
  have hstable : (prefixWord ++ tailWord_4312886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312886).length < 2 ^ (prefixWord ++ tailWord_4312886).sum := by decide
  have hdescent : baseEnd_4312886 < baseStart_4312886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312901 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 4, 6]
def baseStart_4312901 : Nat := 118140960795 + 4312901 * 2 ^ 59
def prefixEnd_4312901 : Nat := 4983230072969 + 3 ^ 40 * 4312901 * 2
def baseEnd_4312901 : Nat := 738197076085645162900945

theorem tailTrace_4312901 : CollatzResearch.WordTrace tailWord_4312901 prefixEnd_4312901 738197076085645162900945 := by
  unfold tailWord_4312901
  simp only [CollatzResearch.WordTrace]
  refine ⟨157304422548103736693394557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104869615032069157795596371 157304422548103736693394557)
  ·
    refine ⟨58989158455538901260022959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157304422548103736693394557 58989158455538901260022959)
    ·
      refine ⟨88483737683308351890034439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58989158455538901260022959 88483737683308351890034439)
      ·
        refine ⟨132725606524962527835051659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88483737683308351890034439 132725606524962527835051659)
        ·
          refine ⟨199088409787443791752577489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132725606524962527835051659 199088409787443791752577489)
          ·
            refine ⟨149316307340582843814433117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199088409787443791752577489 149316307340582843814433117)
            ·
              refine ⟨55993615252718566430412419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149316307340582843814433117 55993615252718566430412419)
              ·
                refine ⟨83990422879077849645618629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 55993615252718566430412419 83990422879077849645618629)
                ·
                  refine ⟨15748204289827096808553493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 83990422879077849645618629 15748204289827096808553493)
                  ·
                    refine ⟨738197076085645162900945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15748204289827096808553493 738197076085645162900945)
                    ·
                      rfl

theorem cell23_4312901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_4312901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312901 prefixEnd_4312901 := by exact prefixLift 4312901
  have htrace : WordTrace (prefixWord ++ tailWord_4312901) baseStart_4312901 baseEnd_4312901 := by
    simpa [prefixWord, tailWord_4312901, baseEnd_4312901] using wordTrace_append hprefix tailTrace_4312901
  have hstable : (prefixWord ++ tailWord_4312901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312901).length < 2 ^ (prefixWord ++ tailWord_4312901).sum := by decide
  have hdescent : baseEnd_4312901 < baseStart_4312901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312919 : List Nat := [1, 1, 3, 2, 5, 1, 3, 1, 2, 1, 3]
def baseStart_4312919 : Nat := 118140960795 + 4312919 * 2 ^ 59
def prefixEnd_4312919 : Nat := 4983230072969 + 3 ^ 40 * 4312919 * 2
def baseEnd_4312919 : Nat := 2214600470908716418277753

theorem tailTrace_4312919 : CollatzResearch.WordTrace tailWord_4312919 prefixEnd_4312919 2214600470908716418277753 := by
  unfold tailWord_4312919
  simp only [CollatzResearch.WordTrace]
  refine ⟨157305079062038525767549811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104870052708025683845033207 157305079062038525767549811)
  ·
    refine ⟨235957618593057788651324717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157305079062038525767549811 235957618593057788651324717)
    ·
      refine ⟨88484106972396670744246769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235957618593057788651324717 88484106972396670744246769)
      ·
        refine ⟨66363080229297503058185077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88484106972396670744246769 66363080229297503058185077)
        ·
          refine ⟨6221538771496640911704851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66363080229297503058185077 6221538771496640911704851)
          ·
            refine ⟨9332308157244961367557277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6221538771496640911704851 9332308157244961367557277)
            ·
              refine ⟨3499615558966860512833979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9332308157244961367557277 3499615558966860512833979)
              ·
                refine ⟨5249423338450290769250969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3499615558966860512833979 5249423338450290769250969)
                ·
                  refine ⟨3937067503837718076938227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5249423338450290769250969 3937067503837718076938227)
                  ·
                    refine ⟨5905601255756577115407341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3937067503837718076938227 5905601255756577115407341)
                    ·
                      refine ⟨2214600470908716418277753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5905601255756577115407341 2214600470908716418277753)
                      ·
                        rfl

theorem cell23_4312919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 2, 1, 3].length) (baseStart_4312919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312919 prefixEnd_4312919 := by exact prefixLift 4312919
  have htrace : WordTrace (prefixWord ++ tailWord_4312919) baseStart_4312919 baseEnd_4312919 := by
    simpa [prefixWord, tailWord_4312919, baseEnd_4312919] using wordTrace_append hprefix tailTrace_4312919
  have hstable : (prefixWord ++ tailWord_4312919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312919).length < 2 ^ (prefixWord ++ tailWord_4312919).sum := by decide
  have hdescent : baseEnd_4312919 < baseStart_4312919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4312951 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 6]
def baseStart_4312951 : Nat := 118140960795 + 4312951 * 2 ^ 59
def prefixEnd_4312951 : Nat := 4983230072969 + 3 ^ 40 * 4312951 * 2
def baseEnd_4312951 : Nat := 2214616902289660293077605

theorem tailTrace_4312951 : CollatzResearch.WordTrace tailWord_4312951 prefixEnd_4312951 2214616902289660293077605 := by
  unfold tailWord_4312951
  simp only [CollatzResearch.WordTrace]
  refine ⟨157306246197922595232714707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104870830798615063488476471 157306246197922595232714707)
  ·
    refine ⟨235959369296883892849072061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157306246197922595232714707 235959369296883892849072061)
    ·
      refine ⟨88484763486331459818402023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235959369296883892849072061 88484763486331459818402023)
      ·
        refine ⟨132727145229497189727603035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88484763486331459818402023 132727145229497189727603035)
        ·
          refine ⟨199090717844245784591404553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132727145229497189727603035 199090717844245784591404553)
          ·
            refine ⟨149318038383184338443553415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199090717844245784591404553 149318038383184338443553415)
            ·
              refine ⟨223977057574776507665330123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149318038383184338443553415 223977057574776507665330123)
              ·
                refine ⟨335965586362164761497995185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223977057574776507665330123 335965586362164761497995185)
                ·
                  refine ⟨251974189771623571123496389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335965586362164761497995185 251974189771623571123496389)
                  ·
                    refine ⟨47245160582179419585655573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 251974189771623571123496389 47245160582179419585655573)
                    ·
                      refine ⟨2214616902289660293077605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47245160582179419585655573 2214616902289660293077605)
                      ·
                        rfl

theorem cell23_4312951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_4312951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4312951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4312951 prefixEnd_4312951 := by exact prefixLift 4312951
  have htrace : WordTrace (prefixWord ++ tailWord_4312951) baseStart_4312951 baseEnd_4312951 := by
    simpa [prefixWord, tailWord_4312951, baseEnd_4312951] using wordTrace_append hprefix tailTrace_4312951
  have hstable : (prefixWord ++ tailWord_4312951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4312951).length < 2 ^ (prefixWord ++ tailWord_4312951).sum := by decide
  have hdescent : baseEnd_4312951 < baseStart_4312951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4312951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313015 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 2, 4, 2]
def baseStart_4313015 : Nat := 118140960795 + 4313015 * 2 ^ 59
def prefixEnd_4313015 : Nat := 4983230072969 + 3 ^ 40 * 4313015 * 2
def baseEnd_4313015 : Nat := 2214649765051548042677311

theorem tailTrace_4313015 : CollatzResearch.WordTrace tailWord_4313015 prefixEnd_4313015 2214649765051548042677311 := by
  unfold tailWord_4313015
  simp only [CollatzResearch.WordTrace]
  refine ⟨157308580469690734163044499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104872386979793822775362999 157308580469690734163044499)
  ·
    refine ⟨235962870704536101244566749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157308580469690734163044499 235962870704536101244566749)
    ·
      refine ⟨88486076514201037966712531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235962870704536101244566749 88486076514201037966712531)
      ·
        refine ⟨132729114771301556950068797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88486076514201037966712531 132729114771301556950068797)
        ·
          refine ⟨49773418039238083856275799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132729114771301556950068797 49773418039238083856275799)
          ·
            refine ⟨74660127058857125784413699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49773418039238083856275799 74660127058857125784413699)
            ·
              refine ⟨111990190588285688676620549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74660127058857125784413699 111990190588285688676620549)
              ·
                refine ⟨20998160735303566626866353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 111990190588285688676620549 20998160735303566626866353)
                ·
                  refine ⟨15748620551477674970149765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20998160735303566626866353 15748620551477674970149765)
                  ·
                    refine ⟨2952866353402064056903081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15748620551477674970149765 2952866353402064056903081)
                    ·
                      refine ⟨2214649765051548042677311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2952866353402064056903081 2214649765051548042677311)
                      ·
                        rfl

theorem cell23_4313015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 4, 2].length) (baseStart_4313015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313015 prefixEnd_4313015 := by exact prefixLift 4313015
  have htrace : WordTrace (prefixWord ++ tailWord_4313015) baseStart_4313015 baseEnd_4313015 := by
    simpa [prefixWord, tailWord_4313015, baseEnd_4313015] using wordTrace_append hprefix tailTrace_4313015
  have hstable : (prefixWord ++ tailWord_4313015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313015).length < 2 ^ (prefixWord ++ tailWord_4313015).sum := by decide
  have hdescent : baseEnd_4313015 < baseStart_4313015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313032 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 2, 4, 2]
def baseStart_4313032 : Nat := 118140960795 + 4313032 * 2 ^ 59
def prefixEnd_4313032 : Nat := 4983230072969 + 3 ^ 40 * 4313032 * 2
def baseEnd_4313032 : Nat := 2214658494222674476164733

theorem tailTrace_4313032 : CollatzResearch.WordTrace tailWord_4313032 prefixEnd_4313032 2214658494222674476164733 := by
  unfold tailWord_4313032
  simp only [CollatzResearch.WordTrace]
  refine ⟨78654600255314573033206675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104872800340419430710942233 78654600255314573033206675)
  ·
    refine ⟨117981900382971859549810013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78654600255314573033206675 117981900382971859549810013)
    ·
      refine ⟨44243212643614447331178755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117981900382971859549810013 44243212643614447331178755)
      ·
        refine ⟨66364818965421670996768133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44243212643614447331178755 66364818965421670996768133)
        ·
          refine ⟨12443403556016563311894025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66364818965421670996768133 12443403556016563311894025)
          ·
            refine ⟨9332552667012422483920519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12443403556016563311894025 9332552667012422483920519)
            ·
              refine ⟨13998829000518633725880779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9332552667012422483920519 13998829000518633725880779)
              ·
                refine ⟨20998243500777950588821169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13998829000518633725880779 20998243500777950588821169)
                ·
                  refine ⟨15748682625583462941615877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20998243500777950588821169 15748682625583462941615877)
                  ·
                    refine ⟨2952877992296899301552977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15748682625583462941615877 2952877992296899301552977)
                    ·
                      refine ⟨2214658494222674476164733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2952877992296899301552977 2214658494222674476164733)
                      ·
                        rfl

theorem cell23_4313032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_4313032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313032 prefixEnd_4313032 := by exact prefixLift 4313032
  have htrace : WordTrace (prefixWord ++ tailWord_4313032) baseStart_4313032 baseEnd_4313032 := by
    simpa [prefixWord, tailWord_4313032, baseEnd_4313032] using wordTrace_append hprefix tailTrace_4313032
  have hstable : (prefixWord ++ tailWord_4313032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313032).length < 2 ^ (prefixWord ++ tailWord_4313032).sum := by decide
  have hdescent : baseEnd_4313032 < baseStart_4313032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313046 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_4313046 : Nat := 118140960795 + 4313046 * 2 ^ 59
def prefixEnd_4313046 : Nat := 4983230072969 + 3 ^ 40 * 4313046 * 2
def baseEnd_4313046 : Nat := 738221894317279140463223

theorem tailTrace_4313046 : CollatzResearch.WordTrace tailWord_4313046 prefixEnd_4313046 738221894317279140463223 := by
  unfold tailWord_4313046
  simp only [CollatzResearch.WordTrace]
  refine ⟨9831856945786151653588937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104873140755052284304948661 9831856945786151653588937)
  ·
    refine ⟨7373892709339613740191703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9831856945786151653588937 7373892709339613740191703)
    ·
      refine ⟨11060839064009420610287555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7373892709339613740191703 11060839064009420610287555)
      ·
        refine ⟨16591258596014130915431333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11060839064009420610287555 16591258596014130915431333)
        ·
          refine ⟨3110860986752649546643375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16591258596014130915431333 3110860986752649546643375)
          ·
            refine ⟨4666291480128974319965063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3110860986752649546643375 4666291480128974319965063)
            ·
              refine ⟨6999437220193461479947595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4666291480128974319965063 6999437220193461479947595)
              ·
                refine ⟨10499155830290192219921393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6999437220193461479947595 10499155830290192219921393)
                ·
                  refine ⟨7874366872717644164941045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10499155830290192219921393 7874366872717644164941045)
                  ·
                    refine ⟨738221894317279140463223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7874366872717644164941045 738221894317279140463223)
                    ·
                      rfl

theorem cell23_4313046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_4313046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313046 prefixEnd_4313046 := by exact prefixLift 4313046
  have htrace : WordTrace (prefixWord ++ tailWord_4313046) baseStart_4313046 baseEnd_4313046 := by
    simpa [prefixWord, tailWord_4313046, baseEnd_4313046] using wordTrace_append hprefix tailTrace_4313046
  have hstable : (prefixWord ++ tailWord_4313046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313046).length < 2 ^ (prefixWord ++ tailWord_4313046).sum := by decide
  have hdescent : baseEnd_4313046 < baseStart_4313046 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313049 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 2, 1, 4]
def baseStart_4313049 : Nat := 118140960795 + 4313049 * 2 ^ 59
def prefixEnd_4313049 : Nat := 4983230072969 + 3 ^ 40 * 4313049 * 2
def baseEnd_4313049 : Nat := 2214667223393800909652155

theorem tailTrace_4313049 : CollatzResearch.WordTrace tailWord_4313049 prefixEnd_4313049 2214667223393800909652155 := by
  unfold tailWord_4313049
  simp only [CollatzResearch.WordTrace]
  refine ⟨157309820551567557969782201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104873213701045038646521467 157309820551567557969782201)
  ·
    refine ⟨117982365413675668477336651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157309820551567557969782201 117982365413675668477336651)
    ·
      refine ⟨176973548120513502716004977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117982365413675668477336651 176973548120513502716004977)
      ·
        refine ⟨132730161090385127037003733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176973548120513502716004977 132730161090385127037003733)
        ·
          refine ⟨3110863150555901414929775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 132730161090385127037003733 3110863150555901414929775)
          ·
            refine ⟨4666294725833852122394663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3110863150555901414929775 4666294725833852122394663)
            ·
              refine ⟨6999442088750778183591995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4666294725833852122394663 6999442088750778183591995)
              ·
                refine ⟨10499163133126167275387993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6999442088750778183591995 10499163133126167275387993)
                ·
                  refine ⟨7874372349844625456540995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10499163133126167275387993 7874372349844625456540995)
                  ·
                    refine ⟨11811558524766938184811493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7874372349844625456540995 11811558524766938184811493)
                    ·
                      refine ⟨2214667223393800909652155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11811558524766938184811493 2214667223393800909652155)
                      ·
                        rfl

theorem cell23_4313049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 2, 1, 4].length) (baseStart_4313049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313049 prefixEnd_4313049 := by exact prefixLift 4313049
  have htrace : WordTrace (prefixWord ++ tailWord_4313049) baseStart_4313049 baseEnd_4313049 := by
    simpa [prefixWord, tailWord_4313049, baseEnd_4313049] using wordTrace_append hprefix tailTrace_4313049
  have hstable : (prefixWord ++ tailWord_4313049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313049).length < 2 ^ (prefixWord ++ tailWord_4313049).sum := by decide
  have hdescent : baseEnd_4313049 < baseStart_4313049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313059 : List Nat := [1, 1, 1, 6, 1, 3, 2, 3, 1, 4]
def baseStart_4313059 : Nat := 118140960795 + 4313059 * 2 ^ 59
def prefixEnd_4313059 : Nat := 4983230072969 + 3 ^ 40 * 4313059 * 2
def baseEnd_4313059 : Nat := 738224119400115290175703

theorem tailTrace_4313059 : CollatzResearch.WordTrace tailWord_4313059 prefixEnd_4313059 738224119400115290175703 := by
  unfold tailWord_4313059
  simp only [CollatzResearch.WordTrace]
  refine ⟨157310185281531329677646231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104873456854354219785097487 157310185281531329677646231)
  ·
    refine ⟨235965277922296994516469347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157310185281531329677646231 235965277922296994516469347)
    ·
      refine ⟨353947916883445491774704021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235965277922296994516469347 353947916883445491774704021)
      ·
        refine ⟨16591308603911507426939251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 353947916883445491774704021 16591308603911507426939251)
        ·
          refine ⟨24886962905867261140408877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16591308603911507426939251 24886962905867261140408877)
          ·
            refine ⟨9332611089700222927653329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24886962905867261140408877 9332611089700222927653329)
            ·
              refine ⟨6999458317275167195739997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9332611089700222927653329 6999458317275167195739997)
              ·
                refine ⟨2624796868978187698402499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6999458317275167195739997 2624796868978187698402499)
                ·
                  refine ⟨3937195303467281547603749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2624796868978187698402499 3937195303467281547603749)
                  ·
                    refine ⟨738224119400115290175703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3937195303467281547603749 738224119400115290175703)
                    ·
                      rfl

theorem cell23_4313059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 3, 1, 4].length) (baseStart_4313059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313059 prefixEnd_4313059 := by exact prefixLift 4313059
  have htrace : WordTrace (prefixWord ++ tailWord_4313059) baseStart_4313059 baseEnd_4313059 := by
    simpa [prefixWord, tailWord_4313059, baseEnd_4313059] using wordTrace_append hprefix tailTrace_4313059
  have hstable : (prefixWord ++ tailWord_4313059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313059).length < 2 ^ (prefixWord ++ tailWord_4313059).sum := by decide
  have hdescent : baseEnd_4313059 < baseStart_4313059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313088 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 4]
def baseStart_4313088 : Nat := 118140960795 + 4313088 * 2 ^ 59
def prefixEnd_4313088 : Nat := 4983230072969 + 3 ^ 40 * 4313088 * 2
def baseEnd_4313088 : Nat := 2214687249139326257064475

theorem tailTrace_4313088 : CollatzResearch.WordTrace tailWord_4313088 prefixEnd_4313088 2214687249139326257064475 := by
  unfold tailWord_4313088
  simp only [CollatzResearch.WordTrace]
  refine ⟨78655621499213133815225959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104874161998950845086967945 78655621499213133815225959)
  ·
    refine ⟨117983432248819700722838939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78655621499213133815225959 117983432248819700722838939)
    ·
      refine ⟨176975148373229551084258409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117983432248819700722838939 176975148373229551084258409)
      ·
        refine ⟨132731361279922163313193807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176975148373229551084258409 132731361279922163313193807)
        ·
          refine ⟨199097041919883244969790711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132731361279922163313193807 199097041919883244969790711)
          ·
            refine ⟨298645562879824867454686067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199097041919883244969790711 298645562879824867454686067)
            ·
              refine ⟨447968344319737301182029101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298645562879824867454686067 447968344319737301182029101)
              ·
                refine ⟨167988129119901487943260913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 447968344319737301182029101 167988129119901487943260913)
                ·
                  refine ⟨125991096839926115957445685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167988129119901487943260913 125991096839926115957445685)
                  ·
                    refine ⟨11811665328743073371010533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 125991096839926115957445685 11811665328743073371010533)
                    ·
                      refine ⟨2214687249139326257064475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11811665328743073371010533 2214687249139326257064475)
                      ·
                        rfl

theorem cell23_4313088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_4313088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313088 prefixEnd_4313088 := by exact prefixLift 4313088
  have htrace : WordTrace (prefixWord ++ tailWord_4313088) baseStart_4313088 baseEnd_4313088 := by
    simpa [prefixWord, tailWord_4313088, baseEnd_4313088] using wordTrace_append hprefix tailTrace_4313088
  have hstable : (prefixWord ++ tailWord_4313088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313088).length < 2 ^ (prefixWord ++ tailWord_4313088).sum := by decide
  have hdescent : baseEnd_4313088 < baseStart_4313088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313102 : List Nat := [4, 1, 1, 2, 2, 1, 4, 2, 1, 5]
def baseStart_4313102 : Nat := 118140960795 + 4313102 * 2 ^ 59
def prefixEnd_4313102 : Nat := 4983230072969 + 3 ^ 40 * 4313102 * 2
def baseEnd_4313102 : Nat := 738231479289496400763137

theorem tailTrace_4313102 : CollatzResearch.WordTrace tailWord_4313102 prefixEnd_4313102 738231479289496400763137 := by
  unfold tailWord_4313102
  simp only [CollatzResearch.WordTrace]
  refine ⟨19663969202546943502682695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104874502413583698680974373 19663969202546943502682695)
  ·
    refine ⟨29495953803820415254024043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19663969202546943502682695 29495953803820415254024043)
    ·
      refine ⟨44243930705730622881036065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29495953803820415254024043 44243930705730622881036065)
      ·
        refine ⟨33182948029297967160777049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44243930705730622881036065 33182948029297967160777049)
        ·
          refine ⟨24887211021973475370582787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33182948029297967160777049 24887211021973475370582787)
          ·
            refine ⟨37330816532960213055874181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24887211021973475370582787 37330816532960213055874181)
            ·
              refine ⟨6999528099930039947976409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37330816532960213055874181 6999528099930039947976409)
              ·
                refine ⟨5249646074947529960982307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6999528099930039947976409 5249646074947529960982307)
                ·
                  refine ⟨7874469112421294941473461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5249646074947529960982307 7874469112421294941473461)
                  ·
                    refine ⟨738231479289496400763137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7874469112421294941473461 738231479289496400763137)
                    ·
                      rfl

theorem cell23_4313102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_4313102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313102 prefixEnd_4313102 := by exact prefixLift 4313102
  have htrace : WordTrace (prefixWord ++ tailWord_4313102) baseStart_4313102 baseEnd_4313102 := by
    simpa [prefixWord, tailWord_4313102, baseEnd_4313102] using wordTrace_append hprefix tailTrace_4313102
  have hstable : (prefixWord ++ tailWord_4313102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313102).length < 2 ^ (prefixWord ++ tailWord_4313102).sum := by decide
  have hdescent : baseEnd_4313102 < baseStart_4313102 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313116 : List Nat := [2, 2, 3, 1, 3, 1, 3, 3, 1, 1, 3]
def baseStart_4313116 : Nat := 118140960795 + 4313116 * 2 ^ 59
def prefixEnd_4313116 : Nat := 4983230072969 + 3 ^ 40 * 4313116 * 2
def baseEnd_4313116 : Nat := 2214701626597652147514347

theorem tailTrace_4313116 : CollatzResearch.WordTrace tailWord_4313116 prefixEnd_4313116 2214701626597652147514347 := by
  unfold tailWord_4313116
  simp only [CollatzResearch.WordTrace]
  refine ⟨78656132121162414206235601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104874842828216552274980801 78656132121162414206235601)
  ·
    refine ⟨58992099090871810654676701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78656132121162414206235601 58992099090871810654676701)
    ·
      refine ⟨22122037159076928995503763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 58992099090871810654676701 22122037159076928995503763)
      ·
        refine ⟨33183055738615393493255645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22122037159076928995503763 33183055738615393493255645)
        ·
          refine ⟨12443645901980772559970867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33183055738615393493255645 12443645901980772559970867)
          ·
            refine ⟨18665468852971158839956301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12443645901980772559970867 18665468852971158839956301)
            ·
              refine ⟨6999550819864184564983613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18665468852971158839956301 6999550819864184564983613)
              ·
                refine ⟨2624831557449069211868855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6999550819864184564983613 2624831557449069211868855)
                ·
                  refine ⟨3937247336173603817803283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2624831557449069211868855 3937247336173603817803283)
                  ·
                    refine ⟨5905871004260405726704925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3937247336173603817803283 5905871004260405726704925)
                    ·
                      refine ⟨2214701626597652147514347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5905871004260405726704925 2214701626597652147514347)
                      ·
                        rfl

theorem cell23_4313116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_4313116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313116 prefixEnd_4313116 := by exact prefixLift 4313116
  have htrace : WordTrace (prefixWord ++ tailWord_4313116) baseStart_4313116 baseEnd_4313116 := by
    simpa [prefixWord, tailWord_4313116, baseEnd_4313116] using wordTrace_append hprefix tailTrace_4313116
  have hstable : (prefixWord ++ tailWord_4313116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313116).length < 2 ^ (prefixWord ++ tailWord_4313116).sum := by decide
  have hdescent : baseEnd_4313116 < baseStart_4313116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313122 : List Nat := [3, 3, 1, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_4313122 : Nat := 118140960795 + 4313122 * 2 ^ 59
def prefixEnd_4313122 : Nat := 4983230072969 + 3 ^ 40 * 4313122 * 2
def baseEnd_4313122 : Nat := 2214704707481579124039319

theorem tailTrace_4313122 : CollatzResearch.WordTrace tailWord_4313122 prefixEnd_4313122 2214704707481579124039319 := by
  unfold tailWord_4313122
  simp only [CollatzResearch.WordTrace]
  refine ⟨39328120770075772859297405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104874988720202060958126413 39328120770075772859297405)
  ·
    refine ⟨14748045288778414822236527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39328120770075772859297405 14748045288778414822236527)
    ·
      refine ⟨22122067933167622233354791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14748045288778414822236527 22122067933167622233354791)
      ·
        refine ⟨33183101899751433350032187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22122067933167622233354791 33183101899751433350032187)
        ·
          refine ⟨49774652849627150025048281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33183101899751433350032187 49774652849627150025048281)
          ·
            refine ⟨37330989637220362518786211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49774652849627150025048281 37330989637220362518786211)
            ·
              refine ⟨55996484455830543778179317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37330989637220362518786211 55996484455830543778179317)
              ·
                refine ⟨5249670417734113479204311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 55996484455830543778179317 5249670417734113479204311)
                ·
                  refine ⟨7874505626601170218806467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5249670417734113479204311 7874505626601170218806467)
                  ·
                    refine ⟨11811758439901755328209701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7874505626601170218806467 11811758439901755328209701)
                    ·
                      refine ⟨2214704707481579124039319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11811758439901755328209701 2214704707481579124039319)
                      ·
                        rfl

theorem cell23_4313122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_4313122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313122 prefixEnd_4313122 := by exact prefixLift 4313122
  have htrace : WordTrace (prefixWord ++ tailWord_4313122) baseStart_4313122 baseEnd_4313122 := by
    simpa [prefixWord, tailWord_4313122, baseEnd_4313122] using wordTrace_append hprefix tailTrace_4313122
  have hstable : (prefixWord ++ tailWord_4313122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313122).length < 2 ^ (prefixWord ++ tailWord_4313122).sum := by decide
  have hdescent : baseEnd_4313122 < baseStart_4313122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313125 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 1, 1, 5]
def baseStart_4313125 : Nat := 118140960795 + 4313125 * 2 ^ 59
def prefixEnd_4313125 : Nat := 4983230072969 + 3 ^ 40 * 4313125 * 2
def baseEnd_4313125 : Nat := 2214706247923542612301805

theorem tailTrace_4313125 : CollatzResearch.WordTrace tailWord_4313125 prefixEnd_4313125 2214706247923542612301805 := by
  unfold tailWord_4313125
  simp only [CollatzResearch.WordTrace]
  refine ⟨157312592499292222949548829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104875061666194815299699219 157312592499292222949548829)
  ·
    refine ⟨58992222187234583606080811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157312592499292222949548829 58992222187234583606080811)
    ·
      refine ⟨88488333280851875409121217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58992222187234583606080811 88488333280851875409121217)
      ·
        refine ⟨66366249960638906556840913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88488333280851875409121217 66366249960638906556840913)
        ·
          refine ⟨49774687470479179917630685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66366249960638906556840913 49774687470479179917630685)
          ·
            refine ⟨18665507801429692469111507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49774687470479179917630685 18665507801429692469111507)
            ·
              refine ⟨27998261702144538703667261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18665507801429692469111507 27998261702144538703667261)
              ·
                refine ⟨10499348138304202013875223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27998261702144538703667261 10499348138304202013875223)
                ·
                  refine ⟨15749022207456303020812835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10499348138304202013875223 15749022207456303020812835)
                  ·
                    refine ⟨23623533311184454531219253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15749022207456303020812835 23623533311184454531219253)
                    ·
                      refine ⟨2214706247923542612301805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23623533311184454531219253 2214706247923542612301805)
                      ·
                        rfl

theorem cell23_4313125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_4313125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313125 prefixEnd_4313125 := by exact prefixLift 4313125
  have htrace : WordTrace (prefixWord ++ tailWord_4313125) baseStart_4313125 baseEnd_4313125 := by
    simpa [prefixWord, tailWord_4313125, baseEnd_4313125] using wordTrace_append hprefix tailTrace_4313125
  have hstable : (prefixWord ++ tailWord_4313125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313125).length < 2 ^ (prefixWord ++ tailWord_4313125).sum := by decide
  have hdescent : baseEnd_4313125 < baseStart_4313125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313139 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 3, 2, 2]
def baseStart_4313139 : Nat := 118140960795 + 4313139 * 2 ^ 59
def prefixEnd_4313139 : Nat := 4983230072969 + 3 ^ 40 * 4313139 * 2
def baseEnd_4313139 : Nat := 2214713436652705557526741

theorem tailTrace_4313139 : CollatzResearch.WordTrace tailWord_4313139 prefixEnd_4313139 2214713436652705557526741 := by
  unfold tailWord_4313139
  simp only [CollatzResearch.WordTrace]
  refine ⟨157313103121241503340558471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104875402080827668893705647 157313103121241503340558471)
  ·
    refine ⟨235969654681862255010837707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157313103121241503340558471 235969654681862255010837707)
    ·
      refine ⟨353954482022793382516256561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235969654681862255010837707 353954482022793382516256561)
      ·
        refine ⟨265465861517095036887192421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353954482022793382516256561 265465861517095036887192421)
        ·
          refine ⟨49774849034455319416348579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 265465861517095036887192421 49774849034455319416348579)
          ·
            refine ⟨74662273551682979124522869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49774849034455319416348579 74662273551682979124522869)
            ·
              refine ⟨6999588145470279292924019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74662273551682979124522869 6999588145470279292924019)
              ·
                refine ⟨10499382218205418939386029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6999588145470279292924019 10499382218205418939386029)
                ·
                  refine ⟨3937268331827032102269761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10499382218205418939386029 3937268331827032102269761)
                  ·
                    refine ⟨2952951248870274076702321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3937268331827032102269761 2952951248870274076702321)
                    ·
                      refine ⟨2214713436652705557526741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2952951248870274076702321 2214713436652705557526741)
                      ·
                        rfl

theorem cell23_4313139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 2, 2].length) (baseStart_4313139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313139 prefixEnd_4313139 := by exact prefixLift 4313139
  have htrace : WordTrace (prefixWord ++ tailWord_4313139) baseStart_4313139 baseEnd_4313139 := by
    simpa [prefixWord, tailWord_4313139, baseEnd_4313139] using wordTrace_append hprefix tailTrace_4313139
  have hstable : (prefixWord ++ tailWord_4313139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313139).length < 2 ^ (prefixWord ++ tailWord_4313139).sum := by decide
  have hdescent : baseEnd_4313139 < baseStart_4313139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313142 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5]
def baseStart_4313142 : Nat := 118140960795 + 4313142 * 2 ^ 59
def prefixEnd_4313142 : Nat := 4983230072969 + 3 ^ 40 * 4313142 * 2
def baseEnd_4313142 : Nat := 2214714977094669045789227

theorem tailTrace_4313142 : CollatzResearch.WordTrace tailWord_4313142 prefixEnd_4313142 2214714977094669045789227 := by
  unfold tailWord_4313142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9832075783764414678307355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104875475026820423235278453 9832075783764414678307355)
  ·
    refine ⟨14748113675646622017461033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9832075783764414678307355 14748113675646622017461033)
    ·
      refine ⟨11061085256734966513095775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14748113675646622017461033 11061085256734966513095775)
      ·
        refine ⟨16591627885102449769643663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11061085256734966513095775 16591627885102449769643663)
        ·
          refine ⟨24887441827653674654465495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16591627885102449769643663 24887441827653674654465495)
          ·
            refine ⟨37331162741480511981698243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24887441827653674654465495 37331162741480511981698243)
            ·
              refine ⟨55996744112220767972547365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37331162741480511981698243 55996744112220767972547365)
              ·
                refine ⟨10499389521041393994852631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 55996744112220767972547365 10499389521041393994852631)
                ·
                  refine ⟨15749084281562090992278947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10499389521041393994852631 15749084281562090992278947)
                  ·
                    refine ⟨23623626422343136488418421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15749084281562090992278947 23623626422343136488418421)
                    ·
                      refine ⟨2214714977094669045789227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23623626422343136488418421 2214714977094669045789227)
                      ·
                        rfl

theorem cell23_4313142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_4313142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313142 prefixEnd_4313142 := by exact prefixLift 4313142
  have htrace : WordTrace (prefixWord ++ tailWord_4313142) baseStart_4313142 baseEnd_4313142 := by
    simpa [prefixWord, tailWord_4313142, baseEnd_4313142] using wordTrace_append hprefix tailTrace_4313142
  have hstable : (prefixWord ++ tailWord_4313142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313142).length < 2 ^ (prefixWord ++ tailWord_4313142).sum := by decide
  have hdescent : baseEnd_4313142 < baseStart_4313142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313189 : List Nat := [1, 3, 1, 3, 2, 2, 1, 4, 2, 1, 3]
def baseStart_4313189 : Nat := 118140960795 + 4313189 * 2 ^ 59
def prefixEnd_4313189 : Nat := 4983230072969 + 3 ^ 40 * 4313189 * 2
def baseEnd_4313189 : Nat := 2214739110685430361901511

theorem tailTrace_4313189 : CollatzResearch.WordTrace tailWord_4313189 prefixEnd_4313189 2214739110685430361901511 := by
  unfold tailWord_4313189
  simp only [CollatzResearch.WordTrace]
  refine ⟨157314926771060361879878621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104876617847373574586585747 157314926771060361879878621)
  ·
    refine ⟨58993097539147635704954483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157314926771060361879878621 58993097539147635704954483)
    ·
      refine ⟨88489646308721453557431725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58993097539147635704954483 88489646308721453557431725)
      ·
        refine ⟨33183617365770545084036897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88489646308721453557431725 33183617365770545084036897)
        ·
          refine ⟨24887713024327908813027673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33183617365770545084036897 24887713024327908813027673)
          ·
            refine ⟨18665784768245931609770755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24887713024327908813027673 18665784768245931609770755)
            ·
              refine ⟨27998677152368897414656133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18665784768245931609770755 27998677152368897414656133)
              ·
                refine ⟨5249751966069168265248025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27998677152368897414656133 5249751966069168265248025)
                ·
                  refine ⟨3937313974551876198936019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5249751966069168265248025 3937313974551876198936019)
                  ·
                    refine ⟨5905970961827814298404029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3937313974551876198936019 5905970961827814298404029)
                    ·
                      refine ⟨2214739110685430361901511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5905970961827814298404029 2214739110685430361901511)
                      ·
                        rfl

theorem cell23_4313189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_4313189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313189 prefixEnd_4313189 := by exact prefixLift 4313189
  have htrace : WordTrace (prefixWord ++ tailWord_4313189) baseStart_4313189 baseEnd_4313189 := by
    simpa [prefixWord, tailWord_4313189, baseEnd_4313189] using wordTrace_append hprefix tailTrace_4313189
  have hstable : (prefixWord ++ tailWord_4313189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313189).length < 2 ^ (prefixWord ++ tailWord_4313189).sum := by decide
  have hdescent : baseEnd_4313189 < baseStart_4313189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313206 : List Nat := [5, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3]
def baseStart_4313206 : Nat := 118140960795 + 4313206 * 2 ^ 59
def prefixEnd_4313206 : Nat := 4983230072969 + 3 ^ 40 * 4313206 * 2
def baseEnd_4313206 : Nat := 2214747839856556795388933

theorem tailTrace_4313206 : CollatzResearch.WordTrace tailWord_4313206 prefixEnd_4313206 2214747839856556795388933 := by
  unfold tailWord_4313206
  simp only [CollatzResearch.WordTrace]
  refine ⟨9832221675749923361452967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104877031207999182522164981 9832221675749923361452967)
  ·
    refine ⟨14748332513624885042179451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9832221675749923361452967 14748332513624885042179451)
    ·
      refine ⟨22122498770437327563269177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14748332513624885042179451 22122498770437327563269177)
      ·
        refine ⟨16591874077827995672451883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22122498770437327563269177 16591874077827995672451883)
        ·
          refine ⟨24887811116741993508677825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16591874077827995672451883 24887811116741993508677825)
          ·
            refine ⟨18665858337556495131508369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24887811116741993508677825 18665858337556495131508369)
            ·
              refine ⟨13999393753167371348631277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18665858337556495131508369 13999393753167371348631277)
              ·
                refine ⟨5249772657437764255736729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13999393753167371348631277 5249772657437764255736729)
                ·
                  refine ⟨3937329493078323191802547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5249772657437764255736729 3937329493078323191802547)
                  ·
                    refine ⟨5905994239617484787703821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3937329493078323191802547 5905994239617484787703821)
                    ·
                      refine ⟨2214747839856556795388933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5905994239617484787703821 2214747839856556795388933)
                      ·
                        rfl

theorem cell23_4313206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_4313206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313206 prefixEnd_4313206 := by exact prefixLift 4313206
  have htrace : WordTrace (prefixWord ++ tailWord_4313206) baseStart_4313206 baseEnd_4313206 := by
    simpa [prefixWord, tailWord_4313206, baseEnd_4313206] using wordTrace_append hprefix tailTrace_4313206
  have hstable : (prefixWord ++ tailWord_4313206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313206).length < 2 ^ (prefixWord ++ tailWord_4313206).sum := by decide
  have hdescent : baseEnd_4313206 < baseStart_4313206 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313225 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 1, 4, 4]
def baseStart_4313225 : Nat := 118140960795 + 4313225 * 2 ^ 59
def prefixEnd_4313225 : Nat := 4983230072969 + 3 ^ 40 * 4313225 * 2
def baseEnd_4313225 : Nat := 2214757595988992221051345

theorem tailTrace_4313225 : CollatzResearch.WordTrace tailWord_4313225 prefixEnd_4313225 2214757595988992221051345 := by
  unfold tailWord_4313225
  simp only [CollatzResearch.WordTrace]
  refine ⟨157316239798929940028189129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104877493199286626685459419 157316239798929940028189129)
  ·
    refine ⟨117987179849197455021141847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157316239798929940028189129 117987179849197455021141847)
    ·
      refine ⟨176980769773796182531712771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 117987179849197455021141847 176980769773796182531712771)
      ·
        refine ⟨265471154660694273797569157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176980769773796182531712771 265471154660694273797569157)
        ·
          refine ⟨49775841498880176337044217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 265471154660694273797569157 49775841498880176337044217)
          ·
            refine ⟨37331881124160132252783163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49775841498880176337044217 37331881124160132252783163)
            ·
              refine ⟨55997821686240198379174745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37331881124160132252783163 55997821686240198379174745)
              ·
                refine ⟨41998366264680148784381059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 55997821686240198379174745 41998366264680148784381059)
                ·
                  refine ⟨62997549397020223176571589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 41998366264680148784381059 62997549397020223176571589)
                  ·
                    refine ⟨11812040511941291845607173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 62997549397020223176571589 11812040511941291845607173)
                    ·
                      refine ⟨2214757595988992221051345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11812040511941291845607173 2214757595988992221051345)
                      ·
                        rfl

theorem cell23_4313225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_4313225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313225 prefixEnd_4313225 := by exact prefixLift 4313225
  have htrace : WordTrace (prefixWord ++ tailWord_4313225) baseStart_4313225 baseEnd_4313225 := by
    simpa [prefixWord, tailWord_4313225, baseEnd_4313225] using wordTrace_append hprefix tailTrace_4313225
  have hstable : (prefixWord ++ tailWord_4313225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313225).length < 2 ^ (prefixWord ++ tailWord_4313225).sum := by decide
  have hdescent : baseEnd_4313225 < baseStart_4313225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313309 : List Nat := [1, 4, 3, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_4313309 : Nat := 118140960795 + 4313309 * 2 ^ 59
def prefixEnd_4313309 : Nat := 4983230072969 + 3 ^ 40 * 4313309 * 2
def baseEnd_4313309 : Nat := 2214800728363969892400959

theorem tailTrace_4313309 : CollatzResearch.WordTrace tailWord_4313309 prefixEnd_4313309 2214800728363969892400959 := by
  unfold tailWord_4313309
  simp only [CollatzResearch.WordTrace]
  refine ⟨157319303530625622374246981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104879535687083748249497987 157319303530625622374246981)
  ·
    refine ⟨29497369411992304195171309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157319303530625622374246981 29497369411992304195171309)
    ·
      refine ⟨11061513529497114073189241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29497369411992304195171309 11061513529497114073189241)
      ·
        refine ⟨8296135147122835554891931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11061513529497114073189241 8296135147122835554891931)
        ·
          refine ⟨12444202720684253332337897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8296135147122835554891931 12444202720684253332337897)
          ·
            refine ⟨9333152040513189999253423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12444202720684253332337897 9333152040513189999253423)
            ·
              refine ⟨13999728060769784998880135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9333152040513189999253423 13999728060769784998880135)
              ·
                refine ⟨20999592091154677498320203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13999728060769784998880135 20999592091154677498320203)
                ·
                  refine ⟨31499388136732016247480305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20999592091154677498320203 31499388136732016247480305)
                  ·
                    refine ⟨23624541102549012185610229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31499388136732016247480305 23624541102549012185610229)
                    ·
                      refine ⟨2214800728363969892400959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23624541102549012185610229 2214800728363969892400959)
                      ·
                        rfl

theorem cell23_4313309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_4313309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313309 prefixEnd_4313309 := by exact prefixLift 4313309
  have htrace : WordTrace (prefixWord ++ tailWord_4313309) baseStart_4313309 baseEnd_4313309 := by
    simpa [prefixWord, tailWord_4313309, baseEnd_4313309] using wordTrace_append hprefix tailTrace_4313309
  have hstable : (prefixWord ++ tailWord_4313309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313309).length < 2 ^ (prefixWord ++ tailWord_4313309).sum := by decide
  have hdescent : baseEnd_4313309 < baseStart_4313309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313335 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 9]
def baseStart_4313335 : Nat := 118140960795 + 4313335 * 2 ^ 59
def prefixEnd_4313335 : Nat := 4983230072969 + 3 ^ 40 * 4313335 * 2
def baseEnd_4313335 : Nat := 2214814078860986790675839

theorem tailTrace_4313335 : CollatzResearch.WordTrace tailWord_4313335 prefixEnd_4313335 2214814078860986790675839 := by
  unfold tailWord_4313335
  simp only [CollatzResearch.WordTrace]
  refine ⟨157320251828531428814693459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104880167885687619209795639 157320251828531428814693459)
  ·
    refine ⟨235980377742797143222040189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157320251828531428814693459 235980377742797143222040189)
    ·
      refine ⟨88492641653548928708265071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 235980377742797143222040189 88492641653548928708265071)
      ·
        refine ⟨132738962480323393062397607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88492641653548928708265071 132738962480323393062397607)
        ·
          refine ⟨199108443720485089593596411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132738962480323393062397607 199108443720485089593596411)
          ·
            refine ⟨298662665580727634390394617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199108443720485089593596411 298662665580727634390394617)
            ·
              refine ⟨223996999185545725792795963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298662665580727634390394617 223996999185545725792795963)
              ·
                refine ⟨335995498778318588689193945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223996999185545725792795963 335995498778318588689193945)
                ·
                  refine ⟨251996624083738941516895459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335995498778318588689193945 251996624083738941516895459)
                  ·
                    refine ⟨377994936125608412275343189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 251996624083738941516895459 377994936125608412275343189)
                    ·
                      refine ⟨2214814078860986790675839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 377994936125608412275343189 2214814078860986790675839)
                      ·
                        rfl

theorem cell23_4313335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_4313335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313335 prefixEnd_4313335 := by exact prefixLift 4313335
  have htrace : WordTrace (prefixWord ++ tailWord_4313335) baseStart_4313335 baseEnd_4313335 := by
    simpa [prefixWord, tailWord_4313335, baseEnd_4313335] using wordTrace_append hprefix tailTrace_4313335
  have hstable : (prefixWord ++ tailWord_4313335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313335).length < 2 ^ (prefixWord ++ tailWord_4313335).sum := by decide
  have hdescent : baseEnd_4313335 < baseStart_4313335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313379 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 1, 5, 2]
def baseStart_4313379 : Nat := 118140960795 + 4313379 * 2 ^ 59
def prefixEnd_4313379 : Nat := 4983230072969 + 3 ^ 40 * 4313379 * 2
def baseEnd_4313379 : Nat := 2214836672009784618525637

theorem tailTrace_4313379 : CollatzResearch.WordTrace tailWord_4313379 prefixEnd_4313379 2214836672009784618525637 := by
  unfold tailWord_4313379
  simp only [CollatzResearch.WordTrace]
  refine ⟨157321856640372024329295191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104881237760248016219530127 157321856640372024329295191)
  ·
    refine ⟨235982784960558036493942787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157321856640372024329295191 235982784960558036493942787)
    ·
      refine ⟨353974177440837054740914181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235982784960558036493942787 353974177440837054740914181)
      ·
        refine ⟨66370158270156947763921409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 353974177440837054740914181 66370158270156947763921409)
        ·
          refine ⟨49777618702617710822941057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66370158270156947763921409 49777618702617710822941057)
          ·
            refine ⟨37333214026963283117205793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49777618702617710822941057 37333214026963283117205793)
            ·
              refine ⟨27999910520222462337904345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37333214026963283117205793 27999910520222462337904345)
              ·
                refine ⟨20999932890166846753428259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27999910520222462337904345 20999932890166846753428259)
                ·
                  refine ⟨31499899335250270130142389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20999932890166846753428259 31499899335250270130142389)
                  ·
                    refine ⟨2953115562679712824700849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31499899335250270130142389 2953115562679712824700849)
                    ·
                      refine ⟨2214836672009784618525637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2953115562679712824700849 2214836672009784618525637)
                      ·
                        rfl

theorem cell23_4313379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_4313379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313379 prefixEnd_4313379 := by exact prefixLift 4313379
  have htrace : WordTrace (prefixWord ++ tailWord_4313379) baseStart_4313379 baseEnd_4313379 := by
    simpa [prefixWord, tailWord_4313379, baseEnd_4313379] using wordTrace_append hprefix tailTrace_4313379
  have hstable : (prefixWord ++ tailWord_4313379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313379).length < 2 ^ (prefixWord ++ tailWord_4313379).sum := by decide
  have hdescent : baseEnd_4313379 < baseStart_4313379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313390 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 2, 2, 3]
def baseStart_4313390 : Nat := 118140960795 + 4313390 * 2 ^ 59
def prefixEnd_4313390 : Nat := 4983230072969 + 3 ^ 40 * 4313390 * 2
def baseEnd_4313390 : Nat := 2214842320296984075488087

theorem tailTrace_4313390 : CollatzResearch.WordTrace tailWord_4313390 prefixEnd_4313390 2214842320296984075488087 := by
  unfold tailWord_4313390
  simp only [CollatzResearch.WordTrace]
  refine ⟨19665282230416521650993203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104881505228888115471963749 19665282230416521650993203)
  ·
    refine ⟨29497923345624782476489805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19665282230416521650993203 29497923345624782476489805)
    ·
      refine ⟨11061721254609293428683677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29497923345624782476489805 11061721254609293428683677)
      ·
        refine ⟨4148145470478485035756379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11061721254609293428683677 4148145470478485035756379)
        ·
          refine ⟨6222218205717727553634569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4148145470478485035756379 6222218205717727553634569)
          ·
            refine ⟨4666663654288295665225927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6222218205717727553634569 4666663654288295665225927)
            ·
              refine ⟨6999995481432443497838891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4666663654288295665225927 6999995481432443497838891)
              ·
                refine ⟨10499993222148665246758337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6999995481432443497838891 10499993222148665246758337)
                ·
                  refine ⟨7874994916611498935068753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10499993222148665246758337 7874994916611498935068753)
                  ·
                    refine ⟨5906246187458624201301565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7874994916611498935068753 5906246187458624201301565)
                    ·
                      refine ⟨2214842320296984075488087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5906246187458624201301565 2214842320296984075488087)
                      ·
                        rfl

theorem cell23_4313390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_4313390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313390 prefixEnd_4313390 := by exact prefixLift 4313390
  have htrace : WordTrace (prefixWord ++ tailWord_4313390) baseStart_4313390 baseEnd_4313390 := by
    simpa [prefixWord, tailWord_4313390, baseEnd_4313390] using wordTrace_append hprefix tailTrace_4313390
  have hstable : (prefixWord ++ tailWord_4313390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313390).length < 2 ^ (prefixWord ++ tailWord_4313390).sum := by decide
  have hdescent : baseEnd_4313390 < baseStart_4313390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313406 : List Nat := [4, 2, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_4313406 : Nat := 118140960795 + 4313406 * 2 ^ 59
def prefixEnd_4313406 : Nat := 4983230072969 + 3 ^ 40 * 4313406 * 2
def baseEnd_4313406 : Nat := 738283511995818670962671

theorem tailTrace_4313406 : CollatzResearch.WordTrace tailWord_4313406 prefixEnd_4313406 738283511995818670962671 := by
  unfold tailWord_4313406
  simp only [CollatzResearch.WordTrace]
  refine ⟨19665355176409275992566009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104881894274182805293685381 19665355176409275992566009)
  ·
    refine ⟨14749016382306956994424507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19665355176409275992566009 14749016382306956994424507)
    ·
      refine ⟨22123524573460435491636761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14749016382306956994424507 22123524573460435491636761)
      ·
        refine ⟨16592643430095326618727571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22123524573460435491636761 16592643430095326618727571)
        ·
          refine ⟨24888965145142989928091357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16592643430095326618727571 24888965145142989928091357)
          ·
            refine ⟨9333361929428621223034259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24888965145142989928091357 9333361929428621223034259)
            ·
              refine ⟨14000042894142931834551389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9333361929428621223034259 14000042894142931834551389)
              ·
                refine ⟨5250016085303599437956771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14000042894142931834551389 5250016085303599437956771)
                ·
                  refine ⟨7875024127955399156935157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5250016085303599437956771 7875024127955399156935157)
                  ·
                    refine ⟨738283511995818670962671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7875024127955399156935157 738283511995818670962671)
                    ·
                      rfl

theorem cell23_4313406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_4313406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313406 prefixEnd_4313406 := by exact prefixLift 4313406
  have htrace : WordTrace (prefixWord ++ tailWord_4313406) baseStart_4313406 baseEnd_4313406 := by
    simpa [prefixWord, tailWord_4313406, baseEnd_4313406] using wordTrace_append hprefix tailTrace_4313406
  have hstable : (prefixWord ++ tailWord_4313406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313406).length < 2 ^ (prefixWord ++ tailWord_4313406).sum := by decide
  have hdescent : baseEnd_4313406 < baseStart_4313406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313419 : List Nat := [1, 1, 1, 1, 3, 1, 1, 8, 2, 4]
def baseStart_4313419 : Nat := 118140960795 + 4313419 * 2 ^ 59
def prefixEnd_4313419 : Nat := 4983230072969 + 3 ^ 40 * 4313419 * 2
def baseEnd_4313419 : Nat := 738285737078654820675151

theorem tailTrace_4313419 : CollatzResearch.WordTrace tailWord_4313419 prefixEnd_4313419 738285737078654820675151 := by
  unfold tailWord_4313419
  simp only [CollatzResearch.WordTrace]
  refine ⟨157323315560227111160751311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104882210373484740773834207 157323315560227111160751311)
  ·
    refine ⟨235984973340340666741126967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157323315560227111160751311 235984973340340666741126967)
    ·
      refine ⟨353977460010511000111690451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235984973340340666741126967 353977460010511000111690451)
      ·
        refine ⟨530966190015766500167535677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353977460010511000111690451 530966190015766500167535677)
        ·
          refine ⟨199112321255912437562825879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 530966190015766500167535677 199112321255912437562825879)
          ·
            refine ⟨298668481883868656344238819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199112321255912437562825879 298668481883868656344238819)
            ·
              refine ⟨448002722825802984516358229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298668481883868656344238819 448002722825802984516358229)
              ·
                refine ⟨5250031908114878724801073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 448002722825802984516358229 5250031908114878724801073)
                ·
                  refine ⟨3937523931086159043600805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5250031908114878724801073 3937523931086159043600805)
                  ·
                    refine ⟨738285737078654820675151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3937523931086159043600805 738285737078654820675151)
                    ·
                      rfl

theorem cell23_4313419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 4].length) (baseStart_4313419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313419 prefixEnd_4313419 := by exact prefixLift 4313419
  have htrace : WordTrace (prefixWord ++ tailWord_4313419) baseStart_4313419 baseEnd_4313419 := by
    simpa [prefixWord, tailWord_4313419, baseEnd_4313419] using wordTrace_append hprefix tailTrace_4313419
  have hstable : (prefixWord ++ tailWord_4313419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313419).length < 2 ^ (prefixWord ++ tailWord_4313419).sum := by decide
  have hdescent : baseEnd_4313419 < baseStart_4313419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313439 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 4]
def baseStart_4313439 : Nat := 118140960795 + 4313439 * 2 ^ 59
def prefixEnd_4313439 : Nat := 4983230072969 + 3 ^ 40 * 4313439 * 2
def baseEnd_4313439 : Nat := 2214867480849054383775361

theorem tailTrace_4313439 : CollatzResearch.WordTrace tailWord_4313439 prefixEnd_4313439 2214867480849054383775361 := by
  unfold tailWord_4313439
  simp only [CollatzResearch.WordTrace]
  refine ⟨157324045020154654576479371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104882696680103103050986247 157324045020154654576479371)
  ·
    refine ⟨235986067530231981864719057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157324045020154654576479371 235986067530231981864719057)
    ·
      refine ⟨176989550647673986398539293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 235986067530231981864719057 176989550647673986398539293)
      ·
        refine ⟨66371081492877744899452235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 176989550647673986398539293 66371081492877744899452235)
        ·
          refine ⟨99556622239316617349178353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66371081492877744899452235 99556622239316617349178353)
          ·
            refine ⟨74667466679487463011883765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99556622239316617349178353 74667466679487463011883765)
            ·
              refine ⟨7000075001201949657364103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74667466679487463011883765 7000075001201949657364103)
              ·
                refine ⟨10500112501802924486046155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7000075001201949657364103 10500112501802924486046155)
                ·
                  refine ⟨15750168752704386729069233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10500112501802924486046155 15750168752704386729069233)
                  ·
                    refine ⟨11812626564528290046801925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15750168752704386729069233 11812626564528290046801925)
                    ·
                      refine ⟨2214867480849054383775361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11812626564528290046801925 2214867480849054383775361)
                      ·
                        rfl

theorem cell23_4313439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_4313439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313439 prefixEnd_4313439 := by exact prefixLift 4313439
  have htrace : WordTrace (prefixWord ++ tailWord_4313439) baseStart_4313439 baseEnd_4313439 := by
    simpa [prefixWord, tailWord_4313439, baseEnd_4313439] using wordTrace_append hprefix tailTrace_4313439
  have hstable : (prefixWord ++ tailWord_4313439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313439).length < 2 ^ (prefixWord ++ tailWord_4313439).sum := by decide
  have hdescent : baseEnd_4313439 < baseStart_4313439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313476 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_4313476 : Nat := 118140960795 + 4313476 * 2 ^ 59
def prefixEnd_4313476 : Nat := 4983230072969 + 3 ^ 40 * 4313476 * 2
def baseEnd_4313476 : Nat := 2214886479633270739012691

theorem tailTrace_4313476 : CollatzResearch.WordTrace tailWord_4313476 prefixEnd_4313476 2214886479633270739012691 := by
  unfold tailWord_4313476
  simp only [CollatzResearch.WordTrace]
  refine ⟨78662697260510304947788141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104883596347347073263717521 78662697260510304947788141)
  ·
    refine ⟨29498511472691364355420553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78662697260510304947788141 29498511472691364355420553)
    ·
      refine ⟨22123883604518523266565415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29498511472691364355420553 22123883604518523266565415)
      ·
        refine ⟨33185825406777784899848123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22123883604518523266565415 33185825406777784899848123)
        ·
          refine ⟨49778738110166677349772185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33185825406777784899848123 49778738110166677349772185)
          ·
            refine ⟨37334053582625008012329139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49778738110166677349772185 37334053582625008012329139)
            ·
              refine ⟨56001080373937512018493709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37334053582625008012329139 56001080373937512018493709)
              ·
                refine ⟨21000405140226567006935141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56001080373937512018493709 21000405140226567006935141)
                ·
                  refine ⟨3937575963792481313800339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21000405140226567006935141 3937575963792481313800339)
                  ·
                    refine ⟨5906363945688721970700509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3937575963792481313800339 5906363945688721970700509)
                    ·
                      refine ⟨2214886479633270739012691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5906363945688721970700509 2214886479633270739012691)
                      ·
                        rfl

theorem cell23_4313476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_4313476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313476 prefixEnd_4313476 := by exact prefixLift 4313476
  have htrace : WordTrace (prefixWord ++ tailWord_4313476) baseStart_4313476 baseEnd_4313476 := by
    simpa [prefixWord, tailWord_4313476, baseEnd_4313476] using wordTrace_append hprefix tailTrace_4313476
  have hstable : (prefixWord ++ tailWord_4313476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313476).length < 2 ^ (prefixWord ++ tailWord_4313476).sum := by decide
  have hdescent : baseEnd_4313476 < baseStart_4313476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313494 : List Nat := [5, 3, 1, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_4313494 : Nat := 118140960795 + 4313494 * 2 ^ 59
def prefixEnd_4313494 : Nat := 4983230072969 + 3 ^ 40 * 4313494 * 2
def baseEnd_4313494 : Nat := 2214895722285051668587609

theorem tailTrace_4313494 : CollatzResearch.WordTrace tailWord_4313494 prefixEnd_4313494 2214895722285051668587609 := by
  unfold tailWord_4313494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9832878189684712435608221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104884034023303599313154357 9832878189684712435608221)
  ·
    refine ⟨3687329321131767163353083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9832878189684712435608221 3687329321131767163353083)
    ·
      refine ⟨5530993981697650745029625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3687329321131767163353083 5530993981697650745029625)
      ·
        refine ⟨4148245486273238058772219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5530993981697650745029625 4148245486273238058772219)
        ·
          refine ⟨6222368229409857088158329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4148245486273238058772219 6222368229409857088158329)
          ·
            refine ⟨4666776172057392816118747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6222368229409857088158329 4666776172057392816118747)
            ·
              refine ⟨7000164258086089224178121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4666776172057392816118747 7000164258086089224178121)
              ·
                refine ⟨5250123193564566918133591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7000164258086089224178121 5250123193564566918133591)
                ·
                  refine ⟨7875184790346850377200387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5250123193564566918133591 7875184790346850377200387)
                  ·
                    refine ⟨11812777185520275565800581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7875184790346850377200387 11812777185520275565800581)
                    ·
                      refine ⟨2214895722285051668587609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11812777185520275565800581 2214895722285051668587609)
                      ·
                        rfl

theorem cell23_4313494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_4313494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313494 prefixEnd_4313494 := by exact prefixLift 4313494
  have htrace : WordTrace (prefixWord ++ tailWord_4313494) baseStart_4313494 baseEnd_4313494 := by
    simpa [prefixWord, tailWord_4313494, baseEnd_4313494] using wordTrace_append hprefix tailTrace_4313494
  have hstable : (prefixWord ++ tailWord_4313494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313494).length < 2 ^ (prefixWord ++ tailWord_4313494).sum := by decide
  have hdescent : baseEnd_4313494 < baseStart_4313494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313514 : List Nat := [3, 1, 6, 1, 1, 1, 3, 1, 1, 2, 3]
def baseStart_4313514 : Nat := 118140960795 + 4313514 * 2 ^ 59
def prefixEnd_4313514 : Nat := 4983230072969 + 3 ^ 40 * 4313514 * 2
def baseEnd_4313514 : Nat := 2214905991898141590337517

theorem tailTrace_4313514 : CollatzResearch.WordTrace tailWord_4313514 prefixEnd_4313514 2214905991898141590337517 := by
  unfold tailWord_4313514
  simp only [CollatzResearch.WordTrace]
  refine ⟨39331695123720735596364899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104884520329921961590306397 39331695123720735596364899)
  ·
    refine ⟨58997542685581103394547349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39331695123720735596364899 58997542685581103394547349)
    ·
      refine ⟨2765509813386614221619407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 58997542685581103394547349 2765509813386614221619407)
      ·
        refine ⟨4148264720079921332429111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2765509813386614221619407 4148264720079921332429111)
        ·
          refine ⟨6222397080119881998643667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4148264720079921332429111 6222397080119881998643667)
          ·
            refine ⟨9333595620179822997965501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6222397080119881998643667 9333595620179822997965501)
            ·
              refine ⟨3500098357567433624237063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9333595620179822997965501 3500098357567433624237063)
              ·
                refine ⟨5250147536351150436355595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3500098357567433624237063 5250147536351150436355595)
                ·
                  refine ⟨7875221304526725654533393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5250147536351150436355595 7875221304526725654533393)
                  ·
                    refine ⟨5906415978395044240900045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7875221304526725654533393 5906415978395044240900045)
                    ·
                      refine ⟨2214905991898141590337517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5906415978395044240900045 2214905991898141590337517)
                      ·
                        rfl

theorem cell23_4313514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_4313514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313514 prefixEnd_4313514 := by exact prefixLift 4313514
  have htrace : WordTrace (prefixWord ++ tailWord_4313514) baseStart_4313514 baseEnd_4313514 := by
    simpa [prefixWord, tailWord_4313514, baseEnd_4313514] using wordTrace_append hprefix tailTrace_4313514
  have hstable : (prefixWord ++ tailWord_4313514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313514).length < 2 ^ (prefixWord ++ tailWord_4313514).sum := by decide
  have hdescent : baseEnd_4313514 < baseStart_4313514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313556 : List Nat := [2, 4, 1, 2, 2, 2, 1, 2, 7]
def baseStart_4313556 : Nat := 118140960795 + 4313556 * 2 ^ 59
def prefixEnd_4313556 : Nat := 4983230072969 + 3 ^ 40 * 4313556 * 2
def baseEnd_4313556 : Nat := 246103062009514491779147

theorem tailTrace_4313556 : CollatzResearch.WordTrace tailWord_4313556 prefixEnd_4313556 246103062009514491779147 := by
  unfold tailWord_4313556
  simp only [CollatzResearch.WordTrace]
  refine ⟨78664156180365391779244261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104885541573820522372325681 78664156180365391779244261)
  ·
    refine ⟨14749529283818510958608299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78664156180365391779244261 14749529283818510958608299)
    ·
      refine ⟨22124293925727766437912449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14749529283818510958608299 22124293925727766437912449)
      ·
        refine ⟨16593220444295824828434337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22124293925727766437912449 16593220444295824828434337)
        ·
          refine ⟨12444915333221868621325753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16593220444295824828434337 12444915333221868621325753)
          ·
            refine ⟨9333686499916401465994315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12444915333221868621325753 9333686499916401465994315)
            ·
              refine ⟨14000529749874602198991473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9333686499916401465994315 14000529749874602198991473)
              ·
                refine ⟨10500397312405951649243605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14000529749874602198991473 10500397312405951649243605)
                ·
                  refine ⟨246103062009514491779147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10500397312405951649243605 246103062009514491779147)
                  ·
                    rfl

theorem cell23_4313556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_4313556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313556 prefixEnd_4313556 := by exact prefixLift 4313556
  have htrace : WordTrace (prefixWord ++ tailWord_4313556) baseStart_4313556 baseEnd_4313556 := by
    simpa [prefixWord, tailWord_4313556, baseEnd_4313556] using wordTrace_append hprefix tailTrace_4313556
  have hstable : (prefixWord ++ tailWord_4313556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313556).length < 2 ^ (prefixWord ++ tailWord_4313556).sum := by decide
  have hdescent : baseEnd_4313556 < baseStart_4313556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313569 : List Nat := [1, 2, 3, 1, 2, 2, 3, 1, 1, 7]
def baseStart_4313569 : Nat := 118140960795 + 4313569 * 2 ^ 59
def prefixEnd_4313569 : Nat := 4983230072969 + 3 ^ 40 * 4313569 * 2
def baseEnd_4313569 : Nat := 738311411111379625049921

theorem tailTrace_4313569 : CollatzResearch.WordTrace tailWord_4313569 prefixEnd_4313569 738311411111379625049921 := by
  unfold tailWord_4313569
  simp only [CollatzResearch.WordTrace]
  refine ⟨157328786509683686778711761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104885857673122457852474507 157328786509683686778711761)
  ·
    refine ⟨117996589882262765084033821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157328786509683686778711761 117996589882262765084033821)
    ·
      refine ⟨44248721205848536906512683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 117996589882262765084033821 44248721205848536906512683)
      ·
        refine ⟨66373081808772805359769025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44248721205848536906512683 66373081808772805359769025)
        ·
          refine ⟨49779811356579604019826769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66373081808772805359769025 49779811356579604019826769)
          ·
            refine ⟨37334858517434703014870077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49779811356579604019826769 37334858517434703014870077)
            ·
              refine ⟨14000571944038013630576279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37334858517434703014870077 14000571944038013630576279)
              ·
                refine ⟨21000857916057020445864419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14000571944038013630576279 21000857916057020445864419)
                ·
                  refine ⟨31501286874085530668796629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21000857916057020445864419 31501286874085530668796629)
                  ·
                    refine ⟨738311411111379625049921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31501286874085530668796629 738311411111379625049921)
                    ·
                      rfl

theorem cell23_4313569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_4313569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313569 prefixEnd_4313569 := by exact prefixLift 4313569
  have htrace : WordTrace (prefixWord ++ tailWord_4313569) baseStart_4313569 baseEnd_4313569 := by
    simpa [prefixWord, tailWord_4313569, baseEnd_4313569] using wordTrace_append hprefix tailTrace_4313569
  have hstable : (prefixWord ++ tailWord_4313569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313569).length < 2 ^ (prefixWord ++ tailWord_4313569).sum := by decide
  have hdescent : baseEnd_4313569 < baseStart_4313569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313619 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 4]
def baseStart_4313619 : Nat := 118140960795 + 4313619 * 2 ^ 59
def prefixEnd_4313619 : Nat := 4983230072969 + 3 ^ 40 * 4313619 * 2
def baseEnd_4313619 : Nat := 2214959907366863679524533

theorem tailTrace_4313619 : CollatzResearch.WordTrace tailWord_4313619 prefixEnd_4313619 2214959907366863679524533 := by
  unfold tailWord_4313619
  simp only [CollatzResearch.WordTrace]
  refine ⟨157330610159502545318031911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104887073439668363545354607 157330610159502545318031911)
  ·
    refine ⟨235995915239253817977047867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157330610159502545318031911 235995915239253817977047867)
    ·
      refine ⟨353993872858880726965571801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235995915239253817977047867 353993872858880726965571801)
      ·
        refine ⟨265495404644160545224178851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353993872858880726965571801 265495404644160545224178851)
        ·
          refine ⟨398243106966240817836268277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265495404644160545224178851 398243106966240817836268277)
          ·
            refine ⟨37335291278085076672150151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 398243106966240817836268277 37335291278085076672150151)
            ·
              refine ⟨56002936917127615008225227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37335291278085076672150151 56002936917127615008225227)
              ·
                refine ⟨84004405375691422512337841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56002936917127615008225227 84004405375691422512337841)
                ·
                  refine ⟨63003304031768566884253381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84004405375691422512337841 63003304031768566884253381)
                  ·
                    refine ⟨11813119505956606290797509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63003304031768566884253381 11813119505956606290797509)
                    ·
                      refine ⟨2214959907366863679524533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11813119505956606290797509 2214959907366863679524533)
                      ·
                        rfl

theorem cell23_4313619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_4313619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313619 prefixEnd_4313619 := by exact prefixLift 4313619
  have htrace : WordTrace (prefixWord ++ tailWord_4313619) baseStart_4313619 baseEnd_4313619 := by
    simpa [prefixWord, tailWord_4313619, baseEnd_4313619] using wordTrace_append hprefix tailTrace_4313619
  have hstable : (prefixWord ++ tailWord_4313619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313619).length < 2 ^ (prefixWord ++ tailWord_4313619).sum := by decide
  have hdescent : baseEnd_4313619 < baseStart_4313619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313626 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3]
def baseStart_4313626 : Nat := 118140960795 + 4313626 * 2 ^ 59
def prefixEnd_4313626 : Nat := 4983230072969 + 3 ^ 40 * 4313626 * 2
def baseEnd_4313626 : Nat := 2214963501731445152137001

theorem tailTrace_4313626 : CollatzResearch.WordTrace tailWord_4313626 prefixEnd_4313626 2214963501731445152137001 := by
  unfold tailWord_4313626
  simp only [CollatzResearch.WordTrace]
  refine ⟨39332716367619296378384183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104887243646984790342357821 39332716367619296378384183)
  ·
    refine ⟨58999074551428944567576275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39332716367619296378384183 58999074551428944567576275)
    ·
      refine ⟨88498611827143416851364413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58999074551428944567576275 88498611827143416851364413)
      ·
        refine ⟨33186979435178781319261655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88498611827143416851364413 33186979435178781319261655)
        ·
          refine ⟨49780469152768171978892483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33186979435178781319261655 49780469152768171978892483)
          ·
            refine ⟨74670703729152257968338725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49780469152768171978892483 74670703729152257968338725)
            ·
              refine ⟨14000756949216048369063511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74670703729152257968338725 14000756949216048369063511)
              ·
                refine ⟨21001135423824072553595267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14000756949216048369063511 21001135423824072553595267)
                ·
                  refine ⟨31501703135736108830392901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21001135423824072553595267 31501703135736108830392901)
                  ·
                    refine ⟨5906569337950520405698669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31501703135736108830392901 5906569337950520405698669)
                    ·
                      refine ⟨2214963501731445152137001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5906569337950520405698669 2214963501731445152137001)
                      ·
                        rfl

theorem cell23_4313626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_4313626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313626 prefixEnd_4313626 := by exact prefixLift 4313626
  have htrace : WordTrace (prefixWord ++ tailWord_4313626) baseStart_4313626 baseEnd_4313626 := by
    simpa [prefixWord, tailWord_4313626, baseEnd_4313626] using wordTrace_append hprefix tailTrace_4313626
  have hstable : (prefixWord ++ tailWord_4313626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313626).length < 2 ^ (prefixWord ++ tailWord_4313626).sum := by decide
  have hdescent : baseEnd_4313626 < baseStart_4313626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313649 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 8]
def baseStart_4313649 : Nat := 118140960795 + 4313649 * 2 ^ 59
def prefixEnd_4313649 : Nat := 4983230072969 + 3 ^ 40 * 4313649 * 2
def baseEnd_4313649 : Nat := 2214975311786498562149395

theorem tailTrace_4313649 : CollatzResearch.WordTrace tailWord_4313649 prefixEnd_4313649 2214975311786498562149395 := by
  unfold tailWord_4313649
  simp only [CollatzResearch.WordTrace]
  refine ⟨157331704349393860441624001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104887802899595906961082667 157331704349393860441624001)
  ·
    refine ⟨117998778262045395331218001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157331704349393860441624001 117998778262045395331218001)
    ·
      refine ⟨88499083696534046498413501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 117998778262045395331218001 88499083696534046498413501)
      ·
        refine ⟨33187156386200267436905063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88499083696534046498413501 33187156386200267436905063)
        ·
          refine ⟨49780734579300401155357595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33187156386200267436905063 49780734579300401155357595)
          ·
            refine ⟨74671101868950601733036393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49780734579300401155357595 74671101868950601733036393)
            ·
              refine ⟨56003326401712951299777295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74671101868950601733036393 56003326401712951299777295)
              ·
                refine ⟨84004989602569426949665943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56003326401712951299777295 84004989602569426949665943)
                ·
                  refine ⟨126007484403854140424498915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84004989602569426949665943 126007484403854140424498915)
                  ·
                    refine ⟨189011226605781210636748373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 126007484403854140424498915 189011226605781210636748373)
                    ·
                      refine ⟨2214975311786498562149395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 189011226605781210636748373 2214975311786498562149395)
                      ·
                        rfl

theorem cell23_4313649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_4313649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313649 prefixEnd_4313649 := by exact prefixLift 4313649
  have htrace : WordTrace (prefixWord ++ tailWord_4313649) baseStart_4313649 baseEnd_4313649 := by
    simpa [prefixWord, tailWord_4313649, baseEnd_4313649] using wordTrace_append hprefix tailTrace_4313649
  have hstable : (prefixWord ++ tailWord_4313649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313649).length < 2 ^ (prefixWord ++ tailWord_4313649).sum := by decide
  have hdescent : baseEnd_4313649 < baseStart_4313649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313676 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 3, 5]
def baseStart_4313676 : Nat := 118140960795 + 4313676 * 2 ^ 59
def prefixEnd_4313676 : Nat := 4983230072969 + 3 ^ 40 * 4313676 * 2
def baseEnd_4313676 : Nat := 738329725254723318837257

theorem tailTrace_4313676 : CollatzResearch.WordTrace tailWord_4313676 prefixEnd_4313676 738329725254723318837257 := by
  unfold tailWord_4313676
  simp only [CollatzResearch.WordTrace]
  refine ⟨78666344560148022026428441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104888459413530696035237921 78666344560148022026428441)
  ·
    refine ⟨58999758420111016519821331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78666344560148022026428441 58999758420111016519821331)
    ·
      refine ⟨88499637630166524779731997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 58999758420111016519821331 88499637630166524779731997)
      ·
        refine ⟨33187364111312446792399499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88499637630166524779731997 33187364111312446792399499)
        ·
          refine ⟨49781046166968670188599249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33187364111312446792399499 49781046166968670188599249)
          ·
            refine ⟨37335784625226502641449437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49781046166968670188599249 37335784625226502641449437)
            ·
              refine ⟨14000919234459938490543539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37335784625226502641449437 14000919234459938490543539)
              ·
                refine ⟨21001378851689907735815309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14000919234459938490543539 21001378851689907735815309)
                ·
                  refine ⟨7875517069383715400930741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21001378851689907735815309 7875517069383715400930741)
                  ·
                    refine ⟨738329725254723318837257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7875517069383715400930741 738329725254723318837257)
                    ·
                      rfl

theorem cell23_4313676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_4313676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313676 prefixEnd_4313676 := by exact prefixLift 4313676
  have htrace : WordTrace (prefixWord ++ tailWord_4313676) baseStart_4313676 baseEnd_4313676 := by
    simpa [prefixWord, tailWord_4313676, baseEnd_4313676] using wordTrace_append hprefix tailTrace_4313676
  have hstable : (prefixWord ++ tailWord_4313676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313676).length < 2 ^ (prefixWord ++ tailWord_4313676).sum := by decide
  have hdescent : baseEnd_4313676 < baseStart_4313676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313706 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 3, 6]
def baseStart_4313706 : Nat := 118140960795 + 4313706 * 2 ^ 59
def prefixEnd_4313706 : Nat := 4983230072969 + 3 ^ 40 * 4313706 * 2
def baseEnd_4313706 : Nat := 738334860061268279712211

theorem tailTrace_4313706 : CollatzResearch.WordTrace tailWord_4313706 prefixEnd_4313706 738334860061268279712211 := by
  unfold tailWord_4313706
  simp only [CollatzResearch.WordTrace]
  refine ⟨39333445827546839794112243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104889188873458239450965981 39333445827546839794112243)
  ·
    refine ⟨59000168741320259691168365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39333445827546839794112243 59000168741320259691168365)
    ·
      refine ⟨22125063277995097384188137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59000168741320259691168365 22125063277995097384188137)
      ·
        refine ⟨16593797458496323038141103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22125063277995097384188137 16593797458496323038141103)
        ·
          refine ⟨24890696187744484557211655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16593797458496323038141103 24890696187744484557211655)
          ·
            refine ⟨37336044281616726835817483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24890696187744484557211655 37336044281616726835817483)
            ·
              refine ⟨56004066422425090253726225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37336044281616726835817483 56004066422425090253726225)
              ·
                refine ⟨42003049816818817690294669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56004066422425090253726225 42003049816818817690294669)
                ·
                  refine ⟨15751143681307056633860501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42003049816818817690294669 15751143681307056633860501)
                  ·
                    refine ⟨738334860061268279712211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15751143681307056633860501 738334860061268279712211)
                    ·
                      rfl

theorem cell23_4313706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_4313706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313706 prefixEnd_4313706 := by exact prefixLift 4313706
  have htrace : WordTrace (prefixWord ++ tailWord_4313706) baseStart_4313706 baseEnd_4313706 := by
    simpa [prefixWord, tailWord_4313706, baseEnd_4313706] using wordTrace_append hprefix tailTrace_4313706
  have hstable : (prefixWord ++ tailWord_4313706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313706).length < 2 ^ (prefixWord ++ tailWord_4313706).sum := by decide
  have hdescent : baseEnd_4313706 < baseStart_4313706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313733 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 3, 2, 3]
def baseStart_4313733 : Nat := 118140960795 + 4313733 * 2 ^ 59
def prefixEnd_4313733 : Nat := 4983230072969 + 3 ^ 40 * 4313733 * 2
def baseEnd_4313733 : Nat := 2215018444161476233499009

theorem tailTrace_4313733 : CollatzResearch.WordTrace tailWord_4313733 prefixEnd_4313733 2215018444161476233499009 := by
  unfold tailWord_4313733
  simp only [CollatzResearch.WordTrace]
  refine ⟨157334768081089542787681853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104889845387393028525121235 157334768081089542787681853)
  ·
    refine ⟨59000538030408578545380695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157334768081089542787681853 59000538030408578545380695)
    ·
      refine ⟨88500807045612867818071043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59000538030408578545380695 88500807045612867818071043)
      ·
        refine ⟨132751210568419301727106565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88500807045612867818071043 132751210568419301727106565)
        ·
          refine ⟨24890851981578619073832481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132751210568419301727106565 24890851981578619073832481)
          ·
            refine ⟨18668138986183964305374361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24890851981578619073832481 18668138986183964305374361)
            ·
              refine ⟨14001104239637973229030771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18668138986183964305374361 14001104239637973229030771)
              ·
                refine ⟨21001656359456959843546157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14001104239637973229030771 21001656359456959843546157)
                ·
                  refine ⟨7875621134796359941329809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21001656359456959843546157 7875621134796359941329809)
                  ·
                    refine ⟨5906715851097269955997357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7875621134796359941329809 5906715851097269955997357)
                    ·
                      refine ⟨2215018444161476233499009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5906715851097269955997357 2215018444161476233499009)
                      ·
                        rfl

theorem cell23_4313733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_4313733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313733 prefixEnd_4313733 := by exact prefixLift 4313733
  have htrace : WordTrace (prefixWord ++ tailWord_4313733) baseStart_4313733 baseEnd_4313733 := by
    simpa [prefixWord, tailWord_4313733, baseEnd_4313733] using wordTrace_append hprefix tailTrace_4313733
  have hstable : (prefixWord ++ tailWord_4313733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313733).length < 2 ^ (prefixWord ++ tailWord_4313733).sum := by decide
  have hdescent : baseEnd_4313733 < baseStart_4313733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313774 : List Nat := [4, 1, 4, 1, 1, 2, 3, 1, 2, 4]
def baseStart_4313774 : Nat := 118140960795 + 4313774 * 2 ^ 59
def prefixEnd_4313774 : Nat := 4983230072969 + 3 ^ 40 * 4313774 * 2
def baseEnd_4313774 : Nat := 738346498956103524362107

theorem tailTrace_4313774 : CollatzResearch.WordTrace tailWord_4313774 prefixEnd_4313774 738346498956103524362107 := by
  unfold tailWord_4313774
  simp only [CollatzResearch.WordTrace]
  refine ⟨19667032934242625848740547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104890842315960671193282917 19667032934242625848740547)
  ·
    refine ⟨29500549401363938773110821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19667032934242625848740547 29500549401363938773110821)
    ·
      refine ⟨5531353012755738519958279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29500549401363938773110821 5531353012755738519958279)
      ·
        refine ⟨8297029519133607779937419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5531353012755738519958279 8297029519133607779937419)
        ·
          refine ⟨12445544278700411669906129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8297029519133607779937419 12445544278700411669906129)
          ·
            refine ⟨9334158209025308752429597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12445544278700411669906129 9334158209025308752429597)
            ·
              refine ⟨3500309328384490782161099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9334158209025308752429597 3500309328384490782161099)
              ·
                refine ⟨5250463992576736173241649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3500309328384490782161099 5250463992576736173241649)
                ·
                  refine ⟨3937847994432552129931237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5250463992576736173241649 3937847994432552129931237)
                  ·
                    refine ⟨738346498956103524362107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3937847994432552129931237 738346498956103524362107)
                    ·
                      rfl

theorem cell23_4313774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_4313774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313774 prefixEnd_4313774 := by exact prefixLift 4313774
  have htrace : WordTrace (prefixWord ++ tailWord_4313774) baseStart_4313774 baseEnd_4313774 := by
    simpa [prefixWord, tailWord_4313774, baseEnd_4313774] using wordTrace_append hprefix tailTrace_4313774
  have hstable : (prefixWord ++ tailWord_4313774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313774).length < 2 ^ (prefixWord ++ tailWord_4313774).sum := by decide
  have hdescent : baseEnd_4313774 < baseStart_4313774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313777 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 1, 2, 4]
def baseStart_4313777 : Nat := 118140960795 + 4313777 * 2 ^ 59
def prefixEnd_4313777 : Nat := 4983230072969 + 3 ^ 40 * 4313777 * 2
def baseEnd_4313777 : Nat := 2215041037310274061348807

theorem tailTrace_4313777 : CollatzResearch.WordTrace tailWord_4313777 prefixEnd_4313777 2215041037310274061348807 := by
  unfold tailWord_4313777
  simp only [CollatzResearch.WordTrace]
  refine ⟨157336372892930138302283585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104890915261953425534855723 157336372892930138302283585)
  ·
    refine ⟨118002279669697603726712689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157336372892930138302283585 118002279669697603726712689)
    ·
      refine ⟨88501709752273202795034517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118002279669697603726712689 88501709752273202795034517)
      ·
        refine ⟨4148517644637806381017243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88501709752273202795034517 4148517644637806381017243)
        ·
          refine ⟨6222776466956709571525865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4148517644637806381017243 6222776466956709571525865)
          ·
            refine ⟨4667082350217532178644399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6222776466956709571525865 4667082350217532178644399)
            ·
              refine ⟨7000623525326298267966599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4667082350217532178644399 7000623525326298267966599)
              ·
                refine ⟨10500935287989447401949899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7000623525326298267966599 10500935287989447401949899)
                ·
                  refine ⟨15751402931984171102924849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10500935287989447401949899 15751402931984171102924849)
                  ·
                    refine ⟨11813552198988128327193637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15751402931984171102924849 11813552198988128327193637)
                    ·
                      refine ⟨2215041037310274061348807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11813552198988128327193637 2215041037310274061348807)
                      ·
                        rfl

theorem cell23_4313777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_4313777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313777 prefixEnd_4313777 := by exact prefixLift 4313777
  have htrace : WordTrace (prefixWord ++ tailWord_4313777) baseStart_4313777 baseEnd_4313777 := by
    simpa [prefixWord, tailWord_4313777, baseEnd_4313777] using wordTrace_append hprefix tailTrace_4313777
  have hstable : (prefixWord ++ tailWord_4313777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313777).length < 2 ^ (prefixWord ++ tailWord_4313777).sum := by decide
  have hdescent : baseEnd_4313777 < baseStart_4313777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313860 : List Nat := [2, 3, 2, 2, 1, 1, 2, 5, 5]
def baseStart_4313860 : Nat := 118140960795 + 4313860 * 2 ^ 59
def prefixEnd_4313860 : Nat := 4983230072969 + 3 ^ 40 * 4313860 * 2
def baseEnd_4313860 : Nat := 246120406244955248512325

theorem tailTrace_4313860 : CollatzResearch.WordTrace tailWord_4313860 prefixEnd_4313860 246120406244955248512325 := by
  unfold tailWord_4313860
  simp only [CollatzResearch.WordTrace]
  refine ⟨78669700075814721738777517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104892933434419628985036689 78669700075814721738777517)
  ·
    refine ⟨29501137528430520652041569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78669700075814721738777517 29501137528430520652041569)
    ·
      refine ⟨22125853146322890489031177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29501137528430520652041569 22125853146322890489031177)
      ·
        refine ⟨16594389859742167866773383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22125853146322890489031177 16594389859742167866773383)
        ·
          refine ⟨24891584789613251800160075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16594389859742167866773383 24891584789613251800160075)
          ·
            refine ⟨37337377184419877700240113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24891584789613251800160075 37337377184419877700240113)
            ·
              refine ⟨28003032888314908275180085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37337377184419877700240113 28003032888314908275180085)
              ·
                refine ⟨2625284333279522650798133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28003032888314908275180085 2625284333279522650798133)
                ·
                  refine ⟨246120406244955248512325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2625284333279522650798133 246120406244955248512325)
                  ·
                    rfl

theorem cell23_4313860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_4313860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313860 prefixEnd_4313860 := by exact prefixLift 4313860
  have htrace : WordTrace (prefixWord ++ tailWord_4313860) baseStart_4313860 baseEnd_4313860 := by
    simpa [prefixWord, tailWord_4313860, baseEnd_4313860] using wordTrace_append hprefix tailTrace_4313860
  have hstable : (prefixWord ++ tailWord_4313860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313860).length < 2 ^ (prefixWord ++ tailWord_4313860).sum := by decide
  have hdescent : baseEnd_4313860 < baseStart_4313860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313873 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 2, 5]
def baseStart_4313873 : Nat := 118140960795 + 4313873 * 2 ^ 59
def prefixEnd_4313873 : Nat := 4983230072969 + 3 ^ 40 * 4313873 * 2
def baseEnd_4313873 : Nat := 738363443817701895249455

theorem tailTrace_4313873 : CollatzResearch.WordTrace tailWord_4313873 prefixEnd_4313873 738363443817701895249455 := by
  unfold tailWord_4313873
  simp only [CollatzResearch.WordTrace]
  refine ⟨157339874300582346697778273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104893249533721564465185515 157339874300582346697778273)
  ·
    refine ⟨118004905725436760023333705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157339874300582346697778273 118004905725436760023333705)
    ·
      refine ⟨88503679294077570017500279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118004905725436760023333705 88503679294077570017500279)
      ·
        refine ⟨132755518941116355026250419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88503679294077570017500279 132755518941116355026250419)
        ·
          refine ⟨199133278411674532539375629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132755518941116355026250419 199133278411674532539375629)
          ·
            refine ⟨74674979404377949702265861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199133278411674532539375629 74674979404377949702265861)
            ·
              refine ⟨14001558638320865569174849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74674979404377949702265861 14001558638320865569174849)
              ·
                refine ⟨10501168978740649176881137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14001558638320865569174849 10501168978740649176881137)
                ·
                  refine ⟨7875876734055486882660853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10501168978740649176881137 7875876734055486882660853)
                  ·
                    refine ⟨738363443817701895249455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7875876734055486882660853 738363443817701895249455)
                    ·
                      rfl

theorem cell23_4313873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_4313873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313873 prefixEnd_4313873 := by exact prefixLift 4313873
  have htrace : WordTrace (prefixWord ++ tailWord_4313873) baseStart_4313873 baseEnd_4313873 := by
    simpa [prefixWord, tailWord_4313873, baseEnd_4313873] using wordTrace_append hprefix tailTrace_4313873
  have hstable : (prefixWord ++ tailWord_4313873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313873).length < 2 ^ (prefixWord ++ tailWord_4313873).sum := by decide
  have hdescent : baseEnd_4313873 < baseStart_4313873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313893 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 1, 3, 4]
def baseStart_4313893 : Nat := 118140960795 + 4313893 * 2 ^ 59
def prefixEnd_4313893 : Nat := 4983230072969 + 3 ^ 40 * 4313893 * 2
def baseEnd_4313893 : Nat := 2215100601066195607498273

theorem tailTrace_4313893 : CollatzResearch.WordTrace tailWord_4313893 prefixEnd_4313893 2215100601066195607498273 := by
  unfold tailWord_4313893
  simp only [CollatzResearch.WordTrace]
  refine ⟨157340603760509890113506333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104893735840339926742337555 157340603760509890113506333)
  ·
    refine ⟨59002726410191208792564875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157340603760509890113506333 59002726410191208792564875)
    ·
      refine ⟨88504089615286813188847313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59002726410191208792564875 88504089615286813188847313)
      ·
        refine ⟨66378067211465109891635485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88504089615286813188847313 66378067211465109891635485)
        ·
          refine ⟨24891775204299416209363307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66378067211465109891635485 24891775204299416209363307)
          ·
            refine ⟨37337662806449124314044961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24891775204299416209363307 37337662806449124314044961)
            ·
              refine ⟨28003247104836843235533721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37337662806449124314044961 28003247104836843235533721)
              ·
                refine ⟨21002435328627632426650291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28003247104836843235533721 21002435328627632426650291)
                ·
                  refine ⟨31503652992941448639975437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21002435328627632426650291 31503652992941448639975437)
                  ·
                    refine ⟨11813869872353043239990789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31503652992941448639975437 11813869872353043239990789)
                    ·
                      refine ⟨2215100601066195607498273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11813869872353043239990789 2215100601066195607498273)
                      ·
                        rfl

theorem cell23_4313893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_4313893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313893 prefixEnd_4313893 := by exact prefixLift 4313893
  have htrace : WordTrace (prefixWord ++ tailWord_4313893) baseStart_4313893 baseEnd_4313893 := by
    simpa [prefixWord, tailWord_4313893, baseEnd_4313893] using wordTrace_append hprefix tailTrace_4313893
  have hstable : (prefixWord ++ tailWord_4313893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313893).length < 2 ^ (prefixWord ++ tailWord_4313893).sum := by decide
  have hdescent : baseEnd_4313893 < baseStart_4313893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313937 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 3, 4]
def baseStart_4313937 : Nat := 118140960795 + 4313937 * 2 ^ 59
def prefixEnd_4313937 : Nat := 4983230072969 + 3 ^ 40 * 4313937 * 2
def baseEnd_4313937 : Nat := 738374398071664478449357

theorem tailTrace_4313937 : CollatzResearch.WordTrace tailWord_4313937 prefixEnd_4313937 738374398071664478449357 := by
  unfold tailWord_4313937
  simp only [CollatzResearch.WordTrace]
  refine ⟨157342208572350485628108065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104894805714900323752072043 157342208572350485628108065)
  ·
    refine ⟨118006656429262864221081049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157342208572350485628108065 118006656429262864221081049)
    ·
      refine ⟨88504992321947148165810787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118006656429262864221081049 88504992321947148165810787)
      ·
        refine ⟨132757488482920722248716181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88504992321947148165810787 132757488482920722248716181)
        ·
          refine ⟨6223007272636908855408571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 132757488482920722248716181 6223007272636908855408571)
          ·
            refine ⟨9334510908955363283112857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6223007272636908855408571 9334510908955363283112857)
            ·
              refine ⟨7000883181716522462334643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9334510908955363283112857 7000883181716522462334643)
              ·
                refine ⟨10501324772574783693501965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7000883181716522462334643 10501324772574783693501965)
                ·
                  refine ⟨3937996789715543885063237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10501324772574783693501965 3937996789715543885063237)
                  ·
                    refine ⟨738374398071664478449357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3937996789715543885063237 738374398071664478449357)
                    ·
                      rfl

theorem cell23_4313937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_4313937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313937 prefixEnd_4313937 := by exact prefixLift 4313937
  have htrace : WordTrace (prefixWord ++ tailWord_4313937) baseStart_4313937 baseEnd_4313937 := by
    simpa [prefixWord, tailWord_4313937, baseEnd_4313937] using wordTrace_append hprefix tailTrace_4313937
  have hstable : (prefixWord ++ tailWord_4313937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313937).length < 2 ^ (prefixWord ++ tailWord_4313937).sum := by decide
  have hdescent : baseEnd_4313937 < baseStart_4313937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313963 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 3, 5]
def baseStart_4313963 : Nat := 118140960795 + 4313963 * 2 ^ 59
def prefixEnd_4313963 : Nat := 4983230072969 + 3 ^ 40 * 4313963 * 2
def baseEnd_4313963 : Nat := 738378848237336777874317

theorem tailTrace_4313963 : CollatzResearch.WordTrace tailWord_4313963 prefixEnd_4313963 738378848237336777874317 := by
  unfold tailWord_4313963
  simp only [CollatzResearch.WordTrace]
  refine ⟨157343156870256292068554543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104895437913504194712369695 157343156870256292068554543)
  ·
    refine ⟨236014735305384438102831815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157343156870256292068554543 236014735305384438102831815)
    ·
      refine ⟨354022102958076657154247723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236014735305384438102831815 354022102958076657154247723)
      ·
        refine ⟨531033154437114985731371585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354022102958076657154247723 531033154437114985731371585)
        ·
          refine ⟨398274865827836239298528689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 531033154437114985731371585 398274865827836239298528689)
          ·
            refine ⟨298706149370877179473896517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398274865827836239298528689 298706149370877179473896517)
            ·
              refine ⟨56007403007039471151355597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 298706149370877179473896517 56007403007039471151355597)
              ·
                refine ⟨21002776127639801681758349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56007403007039471151355597 21002776127639801681758349)
                ·
                  refine ⟨7876041047864925630659381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21002776127639801681758349 7876041047864925630659381)
                  ·
                    refine ⟨738378848237336777874317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7876041047864925630659381 738378848237336777874317)
                    ·
                      rfl

theorem cell23_4313963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 5].length) (baseStart_4313963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313963 prefixEnd_4313963 := by exact prefixLift 4313963
  have htrace : WordTrace (prefixWord ++ tailWord_4313963) baseStart_4313963 baseEnd_4313963 := by
    simpa [prefixWord, tailWord_4313963, baseEnd_4313963] using wordTrace_append hprefix tailTrace_4313963
  have hstable : (prefixWord ++ tailWord_4313963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313963).length < 2 ^ (prefixWord ++ tailWord_4313963).sum := by decide
  have hdescent : baseEnd_4313963 < baseStart_4313963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313987 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 2, 3, 2]
def baseStart_4313987 : Nat := 118140960795 + 4313987 * 2 ^ 59
def prefixEnd_4313987 : Nat := 4983230072969 + 3 ^ 40 * 4313987 * 2
def baseEnd_4313987 : Nat := 2215148868247718239722841

theorem tailTrace_4313987 : CollatzResearch.WordTrace tailWord_4313987 prefixEnd_4313987 2215148868247718239722841 := by
  unfold tailWord_4313987
  simp only [CollatzResearch.WordTrace]
  refine ⟨157344032222169344167428215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104896021481446229444952143 157344032222169344167428215)
  ·
    refine ⟨236016048333254016251142323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157344032222169344167428215 236016048333254016251142323)
    ·
      refine ⟨354024072499881024376713485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236016048333254016251142323 354024072499881024376713485)
      ·
        refine ⟨132759027187455384141267557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 354024072499881024376713485 132759027187455384141267557)
        ·
          refine ⟨24892317597647884526487667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132759027187455384141267557 24892317597647884526487667)
          ·
            refine ⟨37338476396471826789731501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24892317597647884526487667 37338476396471826789731501)
            ·
              refine ⟨14001928648676935046149313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37338476396471826789731501 14001928648676935046149313)
              ·
                refine ⟨10501446486507701284611985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14001928648676935046149313 10501446486507701284611985)
                ·
                  refine ⟨7876084864880775963458989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10501446486507701284611985 7876084864880775963458989)
                  ·
                    refine ⟨2953531824330290986297121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7876084864880775963458989 2953531824330290986297121)
                    ·
                      refine ⟨2215148868247718239722841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2953531824330290986297121 2215148868247718239722841)
                      ·
                        rfl

theorem cell23_4313987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 2, 3, 2].length) (baseStart_4313987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313987 prefixEnd_4313987 := by exact prefixLift 4313987
  have htrace : WordTrace (prefixWord ++ tailWord_4313987) baseStart_4313987 baseEnd_4313987 := by
    simpa [prefixWord, tailWord_4313987, baseEnd_4313987] using wordTrace_append hprefix tailTrace_4313987
  have hstable : (prefixWord ++ tailWord_4313987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313987).length < 2 ^ (prefixWord ++ tailWord_4313987).sum := by decide
  have hdescent : baseEnd_4313987 < baseStart_4313987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4313994 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 3, 1, 3]
def baseStart_4313994 : Nat := 118140960795 + 4313994 * 2 ^ 59
def prefixEnd_4313994 : Nat := 4983230072969 + 3 ^ 40 * 4313994 * 2
def baseEnd_4313994 : Nat := 2215152462612299712335309

theorem tailTrace_4313994 : CollatzResearch.WordTrace tailWord_4313994 prefixEnd_4313994 2215152462612299712335309 := by
  unfold tailWord_4313994
  simp only [CollatzResearch.WordTrace]
  refine ⟨39336071883285996090733259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104896191688762656241955357 39336071883285996090733259)
  ·
    refine ⟨59004107824928994136099889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39336071883285996090733259 59004107824928994136099889)
    ·
      refine ⟨44253080868696745602074917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59004107824928994136099889 44253080868696745602074917)
      ·
        refine ⟨8297452662880639800389047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44253080868696745602074917 8297452662880639800389047)
        ·
          refine ⟨12446178994320959700583571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8297452662880639800389047 12446178994320959700583571)
          ·
            refine ⟨18669268491481439550875357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12446178994320959700583571 18669268491481439550875357)
            ·
              refine ⟨7000975684305539831578259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18669268491481439550875357 7000975684305539831578259)
              ·
                refine ⟨10501463526458309747367389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7000975684305539831578259 10501463526458309747367389)
                ·
                  refine ⟨3938048822421866155262771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10501463526458309747367389 3938048822421866155262771)
                  ·
                    refine ⟨5907073233632799232894157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3938048822421866155262771 5907073233632799232894157)
                    ·
                      refine ⟨2215152462612299712335309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5907073233632799232894157 2215152462612299712335309)
                      ·
                        rfl

theorem cell23_4313994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_4313994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4313994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4313994 prefixEnd_4313994 := by exact prefixLift 4313994
  have htrace : WordTrace (prefixWord ++ tailWord_4313994) baseStart_4313994 baseEnd_4313994 := by
    simpa [prefixWord, tailWord_4313994, baseEnd_4313994] using wordTrace_append hprefix tailTrace_4313994
  have hstable : (prefixWord ++ tailWord_4313994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4313994).length < 2 ^ (prefixWord ++ tailWord_4313994).sum := by decide
  have hdescent : baseEnd_4313994 < baseStart_4313994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4313994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314003 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 5]
def baseStart_4314003 : Nat := 118140960795 + 4314003 * 2 ^ 59
def prefixEnd_4314003 : Nat := 4983230072969 + 3 ^ 40 * 4314003 * 2
def baseEnd_4314003 : Nat := 2215157083938190177122767

theorem tailTrace_4314003 : CollatzResearch.WordTrace tailWord_4314003 prefixEnd_4314003 2215157083938190177122767 := by
  unfold tailWord_4314003
  simp only [CollatzResearch.WordTrace]
  refine ⟨157344615790111378900010663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104896410526740919266673775 157344615790111378900010663)
  ·
    refine ⟨236016923685167068350015995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157344615790111378900010663 236016923685167068350015995)
    ·
      refine ⟨354025385527750602525023993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236016923685167068350015995 354025385527750602525023993)
      ·
        refine ⟨265519039145812951893767995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354025385527750602525023993 265519039145812951893767995)
        ·
          refine ⟨398278558718719427840651993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265519039145812951893767995 398278558718719427840651993)
          ·
            refine ⟨298708919039039570880488995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398278558718719427840651993 298708919039039570880488995)
            ·
              refine ⟨448063378558559356320733493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298708919039039570880488995 448063378558559356320733493)
              ·
                refine ⟨42005941739864939655068765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 448063378558559356320733493 42005941739864939655068765)
                ·
                  refine ⟨15752228152449352370650787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42005941739864939655068765 15752228152449352370650787)
                  ·
                    refine ⟨23628342228674028555976181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15752228152449352370650787 23628342228674028555976181)
                    ·
                      refine ⟨2215157083938190177122767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23628342228674028555976181 2215157083938190177122767)
                      ·
                        rfl

theorem cell23_4314003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_4314003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314003 prefixEnd_4314003 := by exact prefixLift 4314003
  have htrace : WordTrace (prefixWord ++ tailWord_4314003) baseStart_4314003 baseEnd_4314003 := by
    simpa [prefixWord, tailWord_4314003, baseEnd_4314003] using wordTrace_append hprefix tailTrace_4314003
  have hstable : (prefixWord ++ tailWord_4314003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314003).length < 2 ^ (prefixWord ++ tailWord_4314003).sum := by decide
  have hdescent : baseEnd_4314003 < baseStart_4314003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314017 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_4314017 : Nat := 118140960795 + 4314017 * 2 ^ 59
def prefixEnd_4314017 : Nat := 4983230072969 + 3 ^ 40 * 4314017 * 2
def baseEnd_4314017 : Nat := 2215164272667353122347703

theorem tailTrace_4314017 : CollatzResearch.WordTrace tailWord_4314017 prefixEnd_4314017 2215164272667353122347703 := by
  unfold tailWord_4314017
  simp only [CollatzResearch.WordTrace]
  refine ⟨157345126412060659291020305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104896750941373772860680203 157345126412060659291020305)
  ·
    refine ⟨118008844809045494468265229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157345126412060659291020305 118008844809045494468265229)
    ·
      refine ⟨44253316803392060425599461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118008844809045494468265229 44253316803392060425599461)
      ·
        refine ⟨8297496900636011329799899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44253316803392060425599461 8297496900636011329799899)
        ·
          refine ⟨12446245350954016994699849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8297496900636011329799899 12446245350954016994699849)
          ·
            refine ⟨9334684013215512746024887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12446245350954016994699849 9334684013215512746024887)
            ·
              refine ⟨14002026019823269119037331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9334684013215512746024887 14002026019823269119037331)
              ·
                refine ⟨21003039029734903678555997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14002026019823269119037331 21003039029734903678555997)
                ·
                  refine ⟨7876139636150588879458499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21003039029734903678555997 7876139636150588879458499)
                  ·
                    refine ⟨11814209454225883319187749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7876139636150588879458499 11814209454225883319187749)
                    ·
                      refine ⟨2215164272667353122347703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11814209454225883319187749 2215164272667353122347703)
                      ·
                        rfl

theorem cell23_4314017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_4314017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314017 prefixEnd_4314017 := by exact prefixLift 4314017
  have htrace : WordTrace (prefixWord ++ tailWord_4314017) baseStart_4314017 baseEnd_4314017 := by
    simpa [prefixWord, tailWord_4314017, baseEnd_4314017] using wordTrace_append hprefix tailTrace_4314017
  have hstable : (prefixWord ++ tailWord_4314017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314017).length < 2 ^ (prefixWord ++ tailWord_4314017).sum := by decide
  have hdescent : baseEnd_4314017 < baseStart_4314017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314045 : List Nat := [1, 4, 1, 2, 5, 1, 2, 2, 1, 1, 3]
def baseStart_4314045 : Nat := 118140960795 + 4314045 * 2 ^ 59
def prefixEnd_4314045 : Nat := 4983230072969 + 3 ^ 40 * 4314045 * 2
def baseEnd_4314045 : Nat := 2215178650125679012797575

theorem tailTrace_4314045 : CollatzResearch.WordTrace tailWord_4314045 prefixEnd_4314045 2215178650125679012797575 := by
  unfold tailWord_4314045
  simp only [CollatzResearch.WordTrace]
  refine ⟨157346147655959220073039589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104897431770639480048693059 157346147655959220073039589)
  ·
    refine ⟨29502402685492353763694923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157346147655959220073039589 29502402685492353763694923)
    ·
      refine ⟨44253604028238530645542385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29502402685492353763694923 44253604028238530645542385)
      ·
        refine ⟨33190203021178897984156789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44253604028238530645542385 33190203021178897984156789)
        ·
          refine ⟨3111581533235521686014699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33190203021178897984156789 3111581533235521686014699)
          ·
            refine ⟨4667372299853282529022049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3111581533235521686014699 4667372299853282529022049)
            ·
              refine ⟨3500529224889961896766537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4667372299853282529022049 3500529224889961896766537)
              ·
                refine ⟨2625396918667471422574903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3500529224889961896766537 2625396918667471422574903)
                ·
                  refine ⟨3938095378001207133862355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2625396918667471422574903 3938095378001207133862355)
                  ·
                    refine ⟨5907143067001810700793533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3938095378001207133862355 5907143067001810700793533)
                    ·
                      refine ⟨2215178650125679012797575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5907143067001810700793533 2215178650125679012797575)
                      ·
                        rfl

theorem cell23_4314045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 1, 1, 3].length) (baseStart_4314045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314045 prefixEnd_4314045 := by exact prefixLift 4314045
  have htrace : WordTrace (prefixWord ++ tailWord_4314045) baseStart_4314045 baseEnd_4314045 := by
    simpa [prefixWord, tailWord_4314045, baseEnd_4314045] using wordTrace_append hprefix tailTrace_4314045
  have hstable : (prefixWord ++ tailWord_4314045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314045).length < 2 ^ (prefixWord ++ tailWord_4314045).sum := by decide
  have hdescent : baseEnd_4314045 < baseStart_4314045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314085 : List Nat := [1, 3, 1, 6, 1, 1, 2, 3, 1, 2, 2]
def baseStart_4314085 : Nat := 118140960795 + 4314085 * 2 ^ 59
def prefixEnd_4314085 : Nat := 4983230072969 + 3 ^ 40 * 4314085 * 2
def baseEnd_4314085 : Nat := 2215199189351858856297391

theorem tailTrace_4314085 : CollatzResearch.WordTrace tailWord_4314085 prefixEnd_4314085 2215199189351858856297391 := by
  unfold tailWord_4314085
  simp only [CollatzResearch.WordTrace]
  refine ⟨157347606575814306904495709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104898404383876204602997139 157347606575814306904495709)
  ·
    refine ⟨59005352465930365089185891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157347606575814306904495709 59005352465930365089185891)
    ·
      refine ⟨88508028698895547633778837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59005352465930365089185891 88508028698895547633778837)
      ·
        refine ⟨4148813845260728795333383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 88508028698895547633778837 4148813845260728795333383)
        ·
          refine ⟨6223220767891093193000075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4148813845260728795333383 6223220767891093193000075)
          ·
            refine ⟨9334831151836639789500113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6223220767891093193000075 9334831151836639789500113)
            ·
              refine ⟨7001123363877479842125085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9334831151836639789500113 7001123363877479842125085)
              ·
                refine ⟨2625421261454054940796907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7001123363877479842125085 2625421261454054940796907)
                ·
                  refine ⟨3938131892181082411195361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2625421261454054940796907 3938131892181082411195361)
                  ·
                    refine ⟨2953598919135811808396521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3938131892181082411195361 2953598919135811808396521)
                    ·
                      refine ⟨2215199189351858856297391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2953598919135811808396521 2215199189351858856297391)
                      ·
                        rfl

theorem cell23_4314085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_4314085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314085 prefixEnd_4314085 := by exact prefixLift 4314085
  have htrace : WordTrace (prefixWord ++ tailWord_4314085) baseStart_4314085 baseEnd_4314085 := by
    simpa [prefixWord, tailWord_4314085, baseEnd_4314085] using wordTrace_append hprefix tailTrace_4314085
  have hstable : (prefixWord ++ tailWord_4314085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314085).length < 2 ^ (prefixWord ++ tailWord_4314085).sum := by decide
  have hdescent : baseEnd_4314085 < baseStart_4314085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314124 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 1, 4, 2]
def baseStart_4314124 : Nat := 118140960795 + 4314124 * 2 ^ 59
def prefixEnd_4314124 : Nat := 4983230072969 + 3 ^ 40 * 4314124 * 2
def baseEnd_4314124 : Nat := 2215219215097384203709711

theorem tailTrace_4314124 : CollatzResearch.WordTrace tailWord_4314124 prefixEnd_4314124 2215219215097384203709711 := by
  unfold tailWord_4314124
  simp only [CollatzResearch.WordTrace]
  refine ⟨78674514511336508282582713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104899352681782011043443617 78674514511336508282582713)
  ·
    refine ⟨59005885883502381211937035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78674514511336508282582713 59005885883502381211937035)
    ·
      refine ⟨88508828825253571817905553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59005885883502381211937035 88508828825253571817905553)
      ·
        refine ⟨66381621618940178863429165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88508828825253571817905553 66381621618940178863429165)
        ·
          refine ⟨24893108107102567073785937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66381621618940178863429165 24893108107102567073785937)
          ·
            refine ⟨18669831080326925305339453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24893108107102567073785937 18669831080326925305339453)
            ·
              refine ⟨7001186655122596989502295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18669831080326925305339453 7001186655122596989502295)
              ·
                refine ⟨10501779982683895484253443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7001186655122596989502295 10501779982683895484253443)
                ·
                  refine ⟨15752669974025843226380165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10501779982683895484253443 15752669974025843226380165)
                  ·
                    refine ⟨2953625620129845604946281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15752669974025843226380165 2953625620129845604946281)
                    ·
                      refine ⟨2215219215097384203709711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2953625620129845604946281 2215219215097384203709711)
                      ·
                        rfl

theorem cell23_4314124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_4314124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314124 prefixEnd_4314124 := by exact prefixLift 4314124
  have htrace : WordTrace (prefixWord ++ tailWord_4314124) baseStart_4314124 baseEnd_4314124 := by
    simpa [prefixWord, tailWord_4314124, baseEnd_4314124] using wordTrace_append hprefix tailTrace_4314124
  have hstable : (prefixWord ++ tailWord_4314124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314124).length < 2 ^ (prefixWord ++ tailWord_4314124).sum := by decide
  have hdescent : baseEnd_4314124 < baseStart_4314124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314144 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 2, 1, 5]
def baseStart_4314144 : Nat := 118140960795 + 4314144 * 2 ^ 59
def prefixEnd_4314144 : Nat := 4983230072969 + 3 ^ 40 * 4314144 * 2
def baseEnd_4314144 : Nat := 2215229484710474125459619

theorem tailTrace_4314144 : CollatzResearch.WordTrace tailWord_4314144 prefixEnd_4314144 2215229484710474125459619 := by
  unfold tailWord_4314144
  simp only [CollatzResearch.WordTrace]
  refine ⟨78674879241300279990446743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104899838988400373320595657 78674879241300279990446743)
  ·
    refine ⟨118012318861950419985670115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78674879241300279990446743 118012318861950419985670115)
    ·
      refine ⟨177018478292925629978505173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118012318861950419985670115 177018478292925629978505173)
      ·
        refine ⟨4148870584990444452621215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 177018478292925629978505173 4148870584990444452621215)
        ·
          refine ⟨6223305877485666678931823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4148870584990444452621215 6223305877485666678931823)
          ·
            refine ⟨9334958816228500018397735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6223305877485666678931823 9334958816228500018397735)
            ·
              refine ⟨14002438224342750027596603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9334958816228500018397735 14002438224342750027596603)
              ·
                refine ⟨21003657336514125041394905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14002438224342750027596603 21003657336514125041394905)
                ·
                  refine ⟨15752743002385593781046179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21003657336514125041394905 15752743002385593781046179)
                  ·
                    refine ⟨23629114503578390671569269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15752743002385593781046179 23629114503578390671569269)
                    ·
                      refine ⟨2215229484710474125459619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23629114503578390671569269 2215229484710474125459619)
                      ·
                        rfl

theorem cell23_4314144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_4314144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314144 prefixEnd_4314144 := by exact prefixLift 4314144
  have htrace : WordTrace (prefixWord ++ tailWord_4314144) baseStart_4314144 baseEnd_4314144 := by
    simpa [prefixWord, tailWord_4314144, baseEnd_4314144] using wordTrace_append hprefix tailTrace_4314144
  have hstable : (prefixWord ++ tailWord_4314144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314144).length < 2 ^ (prefixWord ++ tailWord_4314144).sum := by decide
  have hdescent : baseEnd_4314144 < baseStart_4314144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314164 : List Nat := [2, 5, 1, 2, 1, 1, 3, 1, 7]
def baseStart_4314164 : Nat := 118140960795 + 4314164 * 2 ^ 59
def prefixEnd_4314164 : Nat := 4983230072969 + 3 ^ 40 * 4314164 * 2
def baseEnd_4314164 : Nat := 246137750480396005245503

theorem tailTrace_4314164 : CollatzResearch.WordTrace tailWord_4314164 prefixEnd_4314164 246137750480396005245503 := by
  unfold tailWord_4314164
  simp only [CollatzResearch.WordTrace]
  refine ⟨78675243971264051698310773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104900325295018735597747697 78675243971264051698310773)
  ·
    refine ⟨7375804122306004846716635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 78675243971264051698310773 7375804122306004846716635)
    ·
      refine ⟨11063706183459007270074953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7375804122306004846716635 11063706183459007270074953)
      ·
        refine ⟨8297779637594255452556215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11063706183459007270074953 8297779637594255452556215)
        ·
          refine ⟨12446669456391383178834323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8297779637594255452556215 12446669456391383178834323)
          ·
            refine ⟨18670004184587074768251485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12446669456391383178834323 18670004184587074768251485)
            ·
              refine ⟨7001251569220153038094307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18670004184587074768251485 7001251569220153038094307)
              ·
                refine ⟨10501877353830229557141461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7001251569220153038094307 10501877353830229557141461)
                ·
                  refine ⟨246137750480396005245503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10501877353830229557141461 246137750480396005245503)
                  ·
                    rfl

theorem cell23_4314164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_4314164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314164 prefixEnd_4314164 := by exact prefixLift 4314164
  have htrace : WordTrace (prefixWord ++ tailWord_4314164) baseStart_4314164 baseEnd_4314164 := by
    simpa [prefixWord, tailWord_4314164, baseEnd_4314164] using wordTrace_append hprefix tailTrace_4314164
  have hstable : (prefixWord ++ tailWord_4314164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314164).length < 2 ^ (prefixWord ++ tailWord_4314164).sum := by decide
  have hdescent : baseEnd_4314164 < baseStart_4314164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314167 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 2, 5, 2]
def baseStart_4314167 : Nat := 118140960795 + 4314167 * 2 ^ 59
def prefixEnd_4314167 : Nat := 4983230072969 + 3 ^ 40 * 4314167 * 2
def baseEnd_4314167 : Nat := 2215241294765527535472013

theorem tailTrace_4314167 : CollatzResearch.WordTrace tailWord_4314167 prefixEnd_4314167 2215241294765527535472013 := by
  unfold tailWord_4314167
  simp only [CollatzResearch.WordTrace]
  refine ⟨157350597361517234908980755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104900398241011489939320503 157350597361517234908980755)
  ·
    refine ⟨236025896042275852363471133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157350597361517234908980755 236025896042275852363471133)
    ·
      refine ⟨88509711015853444636301675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236025896042275852363471133 88509711015853444636301675)
      ·
        refine ⟨132764566523780166954452513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88509711015853444636301675 132764566523780166954452513)
        ·
          refine ⟨99573424892835125215839385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132764566523780166954452513 99573424892835125215839385)
          ·
            refine ⟨74680068669626343911879539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99573424892835125215839385 74680068669626343911879539)
            ·
              refine ⟨112020103004439515867819309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74680068669626343911879539 112020103004439515867819309)
              ·
                refine ⟨42007538626664818450432241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112020103004439515867819309 42007538626664818450432241)
                ·
                  refine ⟨31505653969998613837824181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42007538626664818450432241 31505653969998613837824181)
                  ·
                    refine ⟨2953655059687370047296017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31505653969998613837824181 2953655059687370047296017)
                    ·
                      refine ⟨2215241294765527535472013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2953655059687370047296017 2215241294765527535472013)
                      ·
                        rfl

theorem cell23_4314167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 5, 2].length) (baseStart_4314167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314167 prefixEnd_4314167 := by exact prefixLift 4314167
  have htrace : WordTrace (prefixWord ++ tailWord_4314167) baseStart_4314167 baseEnd_4314167 := by
    simpa [prefixWord, tailWord_4314167, baseEnd_4314167] using wordTrace_append hprefix tailTrace_4314167
  have hstable : (prefixWord ++ tailWord_4314167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314167).length < 2 ^ (prefixWord ++ tailWord_4314167).sum := by decide
  have hdescent : baseEnd_4314167 < baseStart_4314167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314170 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7]
def baseStart_4314170 : Nat := 118140960795 + 4314170 * 2 ^ 59
def prefixEnd_4314170 : Nat := 4983230072969 + 3 ^ 40 * 4314170 * 2
def baseEnd_4314170 : Nat := 2215242835207491023734499

theorem tailTrace_4314170 : CollatzResearch.WordTrace tailWord_4314170 prefixEnd_4314170 2215242835207491023734499 := by
  unfold tailWord_4314170
  simp only [CollatzResearch.WordTrace]
  refine ⟨39337676695126591605334991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104900471187004244280893309 39337676695126591605334991)
  ·
    refine ⟨59006515042689887408002487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39337676695126591605334991 59006515042689887408002487)
    ·
      refine ⟨88509772564034831112003731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59006515042689887408002487 88509772564034831112003731)
      ·
        refine ⟨132764658846052246668005597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88509772564034831112003731 132764658846052246668005597)
        ·
          refine ⟨49786747067269592500502099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132764658846052246668005597 49786747067269592500502099)
          ·
            refine ⟨74680120600904388750753149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49786747067269592500502099 74680120600904388750753149)
            ·
              refine ⟨28005045225339145781532431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74680120600904388750753149 28005045225339145781532431)
              ·
                refine ⟨42007567838008718672298647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28005045225339145781532431 42007567838008718672298647)
                ·
                  refine ⟨63011351757013078008447971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42007567838008718672298647 63011351757013078008447971)
                  ·
                    refine ⟨94517027635519617012671957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63011351757013078008447971 94517027635519617012671957)
                    ·
                      refine ⟨2215242835207491023734499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94517027635519617012671957 2215242835207491023734499)
                      ·
                        rfl

theorem cell23_4314170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_4314170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314170 prefixEnd_4314170 := by exact prefixLift 4314170
  have htrace : WordTrace (prefixWord ++ tailWord_4314170) baseStart_4314170 baseEnd_4314170 := by
    simpa [prefixWord, tailWord_4314170, baseEnd_4314170] using wordTrace_append hprefix tailTrace_4314170
  have hstable : (prefixWord ++ tailWord_4314170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314170).length < 2 ^ (prefixWord ++ tailWord_4314170).sum := by decide
  have hdescent : baseEnd_4314170 < baseStart_4314170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314194 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 2, 5]
def baseStart_4314194 : Nat := 118140960795 + 4314194 * 2 ^ 59
def prefixEnd_4314194 : Nat := 4983230072969 + 3 ^ 40 * 4314194 * 2
def baseEnd_4314194 : Nat := 738418386247732976611463

theorem tailTrace_4314194 : CollatzResearch.WordTrace tailWord_4314194 prefixEnd_4314194 738418386247732976611463 := by
  unfold tailWord_4314194
  simp only [CollatzResearch.WordTrace]
  refine ⟨39337895533104854630053409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104901054754946279013475757 39337895533104854630053409)
  ·
    refine ⟨29503421649828640972540057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39337895533104854630053409 29503421649828640972540057)
    ·
      refine ⟨22127566237371480729405043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29503421649828640972540057 22127566237371480729405043)
      ·
        refine ⟨33191349356057221094107565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22127566237371480729405043 33191349356057221094107565)
        ·
          refine ⟨12446756008521457910290337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33191349356057221094107565 12446756008521457910290337)
          ·
            refine ⟨9335067006391093432717753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12446756008521457910290337 9335067006391093432717753)
            ·
              refine ⟨7001300254793320074538315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9335067006391093432717753 7001300254793320074538315)
              ·
                refine ⟨10501950382189980111807473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7001300254793320074538315 10501950382189980111807473)
                ·
                  refine ⟨7876462786642485083855605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10501950382189980111807473 7876462786642485083855605)
                  ·
                    refine ⟨738418386247732976611463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7876462786642485083855605 738418386247732976611463)
                    ·
                      rfl

theorem cell23_4314194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_4314194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314194 prefixEnd_4314194 := by exact prefixLift 4314194
  have htrace : WordTrace (prefixWord ++ tailWord_4314194) baseStart_4314194 baseEnd_4314194 := by
    simpa [prefixWord, tailWord_4314194, baseEnd_4314194] using wordTrace_append hprefix tailTrace_4314194
  have hstable : (prefixWord ++ tailWord_4314194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314194).length < 2 ^ (prefixWord ++ tailWord_4314194).sum := by decide
  have hdescent : baseEnd_4314194 < baseStart_4314194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314237 : List Nat := [1, 4, 1, 1, 3, 1, 1, 5, 6]
def baseStart_4314237 : Nat := 118140960795 + 4314237 * 2 ^ 59
def prefixEnd_4314237 : Nat := 4983230072969 + 3 ^ 40 * 4314237 * 2
def baseEnd_4314237 : Nat := 246141915379038029066299

theorem tailTrace_4314237 : CollatzResearch.WordTrace tailWord_4314237 prefixEnd_4314237 246141915379038029066299 := by
  unfold tailWord_4314237
  simp only [CollatzResearch.WordTrace]
  refine ⟨157353150471263636864028965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104902100314175757909352643 157353150471263636864028965)
  ·
    refine ⟨29503715713361931912005431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157353150471263636864028965 29503715713361931912005431)
    ·
      refine ⟨44255573570042897868008147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29503715713361931912005431 44255573570042897868008147)
      ·
        refine ⟨66383360355064346802012221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44255573570042897868008147 66383360355064346802012221)
        ·
          refine ⟨24893760133149130050754583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66383360355064346802012221 24893760133149130050754583)
          ·
            refine ⟨37340640199723695076131875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24893760133149130050754583 37340640199723695076131875)
            ·
              refine ⟨56010960299585542614197813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37340640199723695076131875 56010960299585542614197813)
              ·
                refine ⟨5251027528086144620081045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56010960299585542614197813 5251027528086144620081045)
                ·
                  refine ⟨246141915379038029066299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5251027528086144620081045 246141915379038029066299)
                  ·
                    rfl

theorem cell23_4314237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_4314237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314237 prefixEnd_4314237 := by exact prefixLift 4314237
  have htrace : WordTrace (prefixWord ++ tailWord_4314237) baseStart_4314237 baseEnd_4314237 := by
    simpa [prefixWord, tailWord_4314237, baseEnd_4314237] using wordTrace_append hprefix tailTrace_4314237
  have hstable : (prefixWord ++ tailWord_4314237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314237).length < 2 ^ (prefixWord ++ tailWord_4314237).sum := by decide
  have hdescent : baseEnd_4314237 < baseStart_4314237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314248 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 2, 1, 4]
def baseStart_4314248 : Nat := 118140960795 + 4314248 * 2 ^ 59
def prefixEnd_4314248 : Nat := 4983230072969 + 3 ^ 40 * 4314248 * 2
def baseEnd_4314248 : Nat := 2215282886698541718559141

theorem tailTrace_4314248 : CollatzResearch.WordTrace tailWord_4314248 prefixEnd_4314248 2215282886698541718559141 := by
  unfold tailWord_4314248
  simp only [CollatzResearch.WordTrace]
  refine ⟨78676775837111892871339699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104902367782815857161786265 78676775837111892871339699)
  ·
    refine ⟨118015163755667839307009549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78676775837111892871339699 118015163755667839307009549)
    ·
      refine ⟨44255686408375439740128581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118015163755667839307009549 44255686408375439740128581)
      ·
        refine ⟨8297941201570394951274109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44255686408375439740128581 8297941201570394951274109)
        ·
          refine ⟨3111727950588898106727791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8297941201570394951274109 3111727950588898106727791)
          ·
            refine ⟨4667591925883347160091687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3111727950588898106727791 4667591925883347160091687)
            ·
              refine ⟨7001387888825020740137531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4667591925883347160091687 7001387888825020740137531)
              ·
                refine ⟨10502081833237531110206297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7001387888825020740137531 10502081833237531110206297)
                ·
                  refine ⟨7876561374928148332654723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10502081833237531110206297 7876561374928148332654723)
                  ·
                    refine ⟨11814842062392222498982085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7876561374928148332654723 11814842062392222498982085)
                    ·
                      refine ⟨2215282886698541718559141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11814842062392222498982085 2215282886698541718559141)
                      ·
                        rfl

theorem cell23_4314248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_4314248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314248 prefixEnd_4314248 := by exact prefixLift 4314248
  have htrace : WordTrace (prefixWord ++ tailWord_4314248) baseStart_4314248 baseEnd_4314248 := by
    simpa [prefixWord, tailWord_4314248, baseEnd_4314248] using wordTrace_append hprefix tailTrace_4314248
  have hstable : (prefixWord ++ tailWord_4314248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314248).length < 2 ^ (prefixWord ++ tailWord_4314248).sum := by decide
  have hdescent : baseEnd_4314248 < baseStart_4314248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314258 : List Nat := [3, 2, 3, 1, 1, 3, 2, 3, 1, 4]
def baseStart_4314258 : Nat := 118140960795 + 4314258 * 2 ^ 59
def prefixEnd_4314258 : Nat := 4983230072969 + 3 ^ 40 * 4314258 * 2
def baseEnd_4314258 : Nat := 738429340501695559811365

theorem tailTrace_4314258 : CollatzResearch.WordTrace tailWord_4314258 prefixEnd_4314258 738429340501695559811365 := by
  unfold tailWord_4314258
  simp only [CollatzResearch.WordTrace]
  refine ⟨39338479101046889362635857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104902610936125038300362285 39338479101046889362635857)
  ·
    refine ⟨29503859325785167021976893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39338479101046889362635857 29503859325785167021976893)
    ·
      refine ⟨11063947247169437633241335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29503859325785167021976893 11063947247169437633241335)
      ·
        refine ⟨16595920870754156449862003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11063947247169437633241335 16595920870754156449862003)
        ·
          refine ⟨24893881306131234674793005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16595920870754156449862003 24893881306131234674793005)
          ·
            refine ⟨9335205489799213003047377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24893881306131234674793005 9335205489799213003047377)
            ·
              refine ⟨7001404117349409752285533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9335205489799213003047377 7001404117349409752285533)
              ·
                refine ⟨2625526544006028657107075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7001404117349409752285533 2625526544006028657107075)
                ·
                  refine ⟨3938289816009042985660613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2625526544006028657107075 3938289816009042985660613)
                  ·
                    refine ⟨738429340501695559811365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3938289816009042985660613 738429340501695559811365)
                    ·
                      rfl

theorem cell23_4314258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_4314258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314258 prefixEnd_4314258 := by exact prefixLift 4314258
  have htrace : WordTrace (prefixWord ++ tailWord_4314258) baseStart_4314258 baseEnd_4314258 := by
    simpa [prefixWord, tailWord_4314258, baseEnd_4314258] using wordTrace_append hprefix tailTrace_4314258
  have hstable : (prefixWord ++ tailWord_4314258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314258).length < 2 ^ (prefixWord ++ tailWord_4314258).sum := by decide
  have hdescent : baseEnd_4314258 < baseStart_4314258 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314271 : List Nat := [1, 1, 2, 6, 2, 2, 1, 2, 6]
def baseStart_4314271 : Nat := 118140960795 + 4314271 * 2 ^ 59
def prefixEnd_4314271 : Nat := 4983230072969 + 3 ^ 40 * 4314271 * 2
def baseEnd_4314271 : Nat := 246143855194843903174615

theorem tailTrace_4314271 : CollatzResearch.WordTrace tailWord_4314271 prefixEnd_4314271 246143855194843903174615 := by
  unfold tailWord_4314271
  simp only [CollatzResearch.WordTrace]
  refine ⟨157354390553140460670766667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104902927035426973780511111 157354390553140460670766667)
  ·
    refine ⟨236031585829710691006150001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157354390553140460670766667 236031585829710691006150001)
    ·
      refine ⟨177023689372283018254612501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236031585829710691006150001 177023689372283018254612501)
      ·
        refine ⟨8297985439325766480684961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 177023689372283018254612501 8297985439325766480684961)
        ·
          refine ⟨6223489079494324860513721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8297985439325766480684961 6223489079494324860513721)
          ·
            refine ⟨4667616809620743645385291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6223489079494324860513721 4667616809620743645385291)
            ·
              refine ⟨7001425214431115468077937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4667616809620743645385291 7001425214431115468077937)
              ·
                refine ⟨5251068910823336601058453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7001425214431115468077937 5251068910823336601058453)
                ·
                  refine ⟨246143855194843903174615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5251068910823336601058453 246143855194843903174615)
                  ·
                    rfl

theorem cell23_4314271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 2, 1, 2, 6].length) (baseStart_4314271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314271 prefixEnd_4314271 := by exact prefixLift 4314271
  have htrace : WordTrace (prefixWord ++ tailWord_4314271) baseStart_4314271 baseEnd_4314271 := by
    simpa [prefixWord, tailWord_4314271, baseEnd_4314271] using wordTrace_append hprefix tailTrace_4314271
  have hstable : (prefixWord ++ tailWord_4314271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314271).length < 2 ^ (prefixWord ++ tailWord_4314271).sum := by decide
  have hdescent : baseEnd_4314271 < baseStart_4314271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314287 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 4]
def baseStart_4314287 : Nat := 118140960795 + 4314287 * 2 ^ 59
def prefixEnd_4314287 : Nat := 4983230072969 + 3 ^ 40 * 4314287 * 2
def baseEnd_4314287 : Nat := 2215302912444067065971461

theorem tailTrace_4314287 : CollatzResearch.WordTrace tailWord_4314287 prefixEnd_4314287 2215302912444067065971461 := by
  unfold tailWord_4314287
  simp only [CollatzResearch.WordTrace]
  refine ⟨157354974121082495403349115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104903316080721663602232743 157354974121082495403349115)
  ·
    refine ⟨236032461181623743105023673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157354974121082495403349115 236032461181623743105023673)
    ·
      refine ⟨177024345886217807328767755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236032461181623743105023673 177024345886217807328767755)
      ·
        refine ⟨265536518829326710993151633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177024345886217807328767755 265536518829326710993151633)
        ·
          refine ⟨199152389121995033244863725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265536518829326710993151633 199152389121995033244863725)
          ·
            refine ⟨74682145920748137466823897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199152389121995033244863725 74682145920748137466823897)
            ·
              refine ⟨56011609440561103100117923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74682145920748137466823897 56011609440561103100117923)
              ·
                refine ⟨84017414160841654650176885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56011609440561103100117923 84017414160841654650176885)
                ·
                  refine ⟨7876632577578905123454083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84017414160841654650176885 7876632577578905123454083)
                  ·
                    refine ⟨11814948866368357685181125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7876632577578905123454083 11814948866368357685181125)
                    ·
                      refine ⟨2215302912444067065971461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11814948866368357685181125 2215302912444067065971461)
                      ·
                        rfl

theorem cell23_4314287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 1, 4].length) (baseStart_4314287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314287 prefixEnd_4314287 := by exact prefixLift 4314287
  have htrace : WordTrace (prefixWord ++ tailWord_4314287) baseStart_4314287 baseEnd_4314287 := by
    simpa [prefixWord, tailWord_4314287, baseEnd_4314287] using wordTrace_append hprefix tailTrace_4314287
  have hstable : (prefixWord ++ tailWord_4314287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314287).length < 2 ^ (prefixWord ++ tailWord_4314287).sum := by decide
  have hdescent : baseEnd_4314287 < baseStart_4314287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314314 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 4, 4]
def baseStart_4314314 : Nat := 118140960795 + 4314314 * 2 ^ 59
def prefixEnd_4314314 : Nat := 4983230072969 + 3 ^ 40 * 4314314 * 2
def baseEnd_4314314 : Nat := 738438925473912820111279

theorem tailTrace_4314314 : CollatzResearch.WordTrace tailWord_4314314 prefixEnd_4314314 738438925473912820111279 := by
  unfold tailWord_4314314
  simp only [CollatzResearch.WordTrace]
  refine ⟨39338989722996169753645499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104903972594656452676387997 39338989722996169753645499)
  ·
    refine ⟨59008484584494254630468249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39338989722996169753645499 59008484584494254630468249)
    ·
      refine ⟨44256363438370690972851187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59008484584494254630468249 44256363438370690972851187)
      ·
        refine ⟨66384545157556036459276781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44256363438370690972851187 66384545157556036459276781)
        ·
          refine ⟨24894204434083513672228793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66384545157556036459276781 24894204434083513672228793)
          ·
            refine ⟨18670653325562635254171595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24894204434083513672228793 18670653325562635254171595)
            ·
              refine ⟨28005979988343952881257393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18670653325562635254171595 28005979988343952881257393)
              ·
                refine ⟨21004484991257964660943045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28005979988343952881257393 21004484991257964660943045)
                ·
                  refine ⟨3938340935860868373926821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21004484991257964660943045 3938340935860868373926821)
                  ·
                    refine ⟨738438925473912820111279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3938340935860868373926821 738438925473912820111279)
                    ·
                      rfl

theorem cell23_4314314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_4314314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314314 prefixEnd_4314314 := by exact prefixLift 4314314
  have htrace : WordTrace (prefixWord ++ tailWord_4314314) baseStart_4314314 baseEnd_4314314 := by
    simpa [prefixWord, tailWord_4314314, baseEnd_4314314] using wordTrace_append hprefix tailTrace_4314314
  have hstable : (prefixWord ++ tailWord_4314314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314314).length < 2 ^ (prefixWord ++ tailWord_4314314).sum := by decide
  have hdescent : baseEnd_4314314 < baseStart_4314314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314348 : List Nat := [2, 2, 1, 1, 2, 6, 2, 1, 2, 4]
def baseStart_4314348 : Nat := 118140960795 + 4314348 * 2 ^ 59
def prefixEnd_4314348 : Nat := 4983230072969 + 3 ^ 40 * 4314348 * 2
def baseEnd_4314348 : Nat := 738444744921330442436227

theorem tailTrace_4314348 : CollatzResearch.WordTrace tailWord_4314348 prefixEnd_4314348 738444744921330442436227 := by
  unfold tailWord_4314348
  simp only [CollatzResearch.WordTrace]
  refine ⟨78678599486930751410659849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104904799315907668547546465 78678599486930751410659849)
  ·
    refine ⟨59008949615198063557994887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78678599486930751410659849 59008949615198063557994887)
    ·
      refine ⟨88513424422797095336992331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59008949615198063557994887 88513424422797095336992331)
      ·
        refine ⟨132770136634195643005488497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88513424422797095336992331 132770136634195643005488497)
        ·
          refine ⟨99577602475646732254116373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132770136634195643005488497 99577602475646732254116373)
          ·
            refine ⟨4667700116045940574411705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 99577602475646732254116373 4667700116045940574411705)
            ·
              refine ⟨3500775087034455430808779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4667700116045940574411705 3500775087034455430808779)
              ·
                refine ⟨5251162630551683146213169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3500775087034455430808779 5251162630551683146213169)
                ·
                  refine ⟨3938371972913762359659877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5251162630551683146213169 3938371972913762359659877)
                  ·
                    refine ⟨738444744921330442436227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3938371972913762359659877 738444744921330442436227)
                    ·
                      rfl

theorem cell23_4314348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_4314348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314348 prefixEnd_4314348 := by exact prefixLift 4314348
  have htrace : WordTrace (prefixWord ++ tailWord_4314348) baseStart_4314348 baseEnd_4314348 := by
    simpa [prefixWord, tailWord_4314348, baseEnd_4314348] using wordTrace_append hprefix tailTrace_4314348
  have hstable : (prefixWord ++ tailWord_4314348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314348).length < 2 ^ (prefixWord ++ tailWord_4314348).sum := by decide
  have hdescent : baseEnd_4314348 < baseStart_4314348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314394 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4]
def baseStart_4314394 : Nat := 118140960795 + 4314394 * 2 ^ 59
def prefixEnd_4314394 : Nat := 4983230072969 + 3 ^ 40 * 4314394 * 2
def baseEnd_4314394 : Nat := 2215357854874098147333469

theorem tailTrace_4314394 : CollatzResearch.WordTrace tailWord_4314394 prefixEnd_4314394 2215357854874098147333469 := by
  unfold tailWord_4314394
  simp only [CollatzResearch.WordTrace]
  refine ⟨39339719182923713169373559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104905917821129901784996157 39339719182923713169373559)
  ·
    refine ⟨59009578774385569754060339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39339719182923713169373559 59009578774385569754060339)
    ·
      refine ⟨88514368161578354631090509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59009578774385569754060339 88514368161578354631090509)
      ·
        refine ⟨33192888060591882986658941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88514368161578354631090509 33192888060591882986658941)
        ·
          refine ⟨12447333022721956119997103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33192888060591882986658941 12447333022721956119997103)
          ·
            refine ⟨18670999534082934179995655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12447333022721956119997103 18670999534082934179995655)
            ·
              refine ⟨28006499301124401269993483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18670999534082934179995655 28006499301124401269993483)
              ·
                refine ⟨42009748951686601904990225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28006499301124401269993483 42009748951686601904990225)
                ·
                  refine ⟨31507311713764951428742669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42009748951686601904990225 31507311713764951428742669)
                  ·
                    refine ⟨11815241892661856785778501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31507311713764951428742669 11815241892661856785778501)
                    ·
                      refine ⟨2215357854874098147333469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11815241892661856785778501 2215357854874098147333469)
                      ·
                        rfl

theorem cell23_4314394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_4314394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314394 prefixEnd_4314394 := by exact prefixLift 4314394
  have htrace : WordTrace (prefixWord ++ tailWord_4314394) baseStart_4314394 baseEnd_4314394 := by
    simpa [prefixWord, tailWord_4314394, baseEnd_4314394] using wordTrace_append hprefix tailTrace_4314394
  have hstable : (prefixWord ++ tailWord_4314394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314394).length < 2 ^ (prefixWord ++ tailWord_4314394).sum := by decide
  have hdescent : baseEnd_4314394 < baseStart_4314394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314404 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 2, 6]
def baseStart_4314404 : Nat := 118140960795 + 4314404 * 2 ^ 59
def prefixEnd_4314404 : Nat := 4983230072969 + 3 ^ 40 * 4314404 * 2
def baseEnd_4314404 : Nat := 738454329893547702736141

theorem tailTrace_4314404 : CollatzResearch.WordTrace tailWord_4314404 prefixEnd_4314404 738454329893547702736141 := by
  unfold tailWord_4314404
  simp only [CollatzResearch.WordTrace]
  refine ⟨78679620730829312192679133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104906160974439082923572177 78679620730829312192679133)
  ·
    refine ⟨29504857774060992072254675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78679620730829312192679133 29504857774060992072254675)
    ·
      refine ⟨44257286661091488108382013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29504857774060992072254675 44257286661091488108382013)
      ·
        refine ⟨16596482497909308040643255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44257286661091488108382013 16596482497909308040643255)
        ·
          refine ⟨24894723746863962060964883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16596482497909308040643255 24894723746863962060964883)
          ·
            refine ⟨37342085620295943091447325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24894723746863962060964883 37342085620295943091447325)
            ·
              refine ⟨14003282107610978659292747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37342085620295943091447325 14003282107610978659292747)
              ·
                refine ⟨21004923161416467988939121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14003282107610978659292747 21004923161416467988939121)
                ·
                  refine ⟨15753692371062350991704341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21004923161416467988939121 15753692371062350991704341)
                  ·
                    refine ⟨738454329893547702736141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15753692371062350991704341 738454329893547702736141)
                    ·
                      rfl

theorem cell23_4314404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_4314404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314404 prefixEnd_4314404 := by exact prefixLift 4314404
  have htrace : WordTrace (prefixWord ++ tailWord_4314404) baseStart_4314404 baseEnd_4314404 := by
    simpa [prefixWord, tailWord_4314404, baseEnd_4314404] using wordTrace_append hprefix tailTrace_4314404
  have hstable : (prefixWord ++ tailWord_4314404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314404).length < 2 ^ (prefixWord ++ tailWord_4314404).sum := by decide
  have hdescent : baseEnd_4314404 < baseStart_4314404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314464 : List Nat := [2, 1, 1, 3, 4, 1, 1, 2, 1, 7]
def baseStart_4314464 : Nat := 118140960795 + 4314464 * 2 ^ 59
def prefixEnd_4314464 : Nat := 4983230072969 + 3 ^ 40 * 4314464 * 2
def baseEnd_4314464 : Nat := 738464599506637624486049

theorem tailTrace_4314464 : CollatzResearch.WordTrace tailWord_4314464 prefixEnd_4314464 738464599506637624486049 := by
  unfold tailWord_4314464
  simp only [CollatzResearch.WordTrace]
  refine ⟨78680714920720627316271223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104907619894294169755028297 78680714920720627316271223)
  ·
    refine ⟨118021072381080940974406835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78680714920720627316271223 118021072381080940974406835)
    ·
      refine ⟨177031608571621411461610253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118021072381080940974406835 177031608571621411461610253)
      ·
        refine ⟨66386853214358029298103845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177031608571621411461610253 66386853214358029298103845)
        ·
          refine ⟨12447534977692130493394471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66386853214358029298103845 12447534977692130493394471)
          ·
            refine ⟨18671302466538195740091707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12447534977692130493394471 18671302466538195740091707)
            ·
              refine ⟨28006953699807293610137561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18671302466538195740091707 28006953699807293610137561)
              ·
                refine ⟨21005215274855470207603171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28006953699807293610137561 21005215274855470207603171)
                ·
                  refine ⟨31507822912283205311404757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21005215274855470207603171 31507822912283205311404757)
                  ·
                    refine ⟨738464599506637624486049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31507822912283205311404757 738464599506637624486049)
                    ·
                      rfl

theorem cell23_4314464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 1, 7].length) (baseStart_4314464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314464 prefixEnd_4314464 := by exact prefixLift 4314464
  have htrace : WordTrace (prefixWord ++ tailWord_4314464) baseStart_4314464 baseEnd_4314464 := by
    simpa [prefixWord, tailWord_4314464, baseEnd_4314464] using wordTrace_append hprefix tailTrace_4314464
  have hstable : (prefixWord ++ tailWord_4314464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314464).length < 2 ^ (prefixWord ++ tailWord_4314464).sum := by decide
  have hdescent : baseEnd_4314464 < baseStart_4314464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314485 : List Nat := [1, 3, 4, 1, 3, 2, 1, 3, 5]
def baseStart_4314485 : Nat := 118140960795 + 4314485 * 2 ^ 59
def prefixEnd_4314485 : Nat := 4983230072969 + 3 ^ 40 * 4314485 * 2
def baseEnd_4314485 : Nat := 246156064623739699032839

theorem tailTrace_4314485 : CollatzResearch.WordTrace tailWord_4314485 prefixEnd_4314485 246156064623739699032839 := by
  unfold tailWord_4314485
  simp only [CollatzResearch.WordTrace]
  refine ⟨157362195774365175219056909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104908130516243450146037939 157362195774365175219056909)
  ·
    refine ⟨59010823415386940707146341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157362195774365175219056909 59010823415386940707146341)
    ·
      refine ⟨11064529390385051382589939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59010823415386940707146341 11064529390385051382589939)
      ·
        refine ⟨16596794085577577073884909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11064529390385051382589939 16596794085577577073884909)
        ·
          refine ⟨6223797782091591402706841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16596794085577577073884909 6223797782091591402706841)
          ·
            refine ⟨4667848336568693552030131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6223797782091591402706841 4667848336568693552030131)
            ·
              refine ⟨7001772504853040328045197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4667848336568693552030131 7001772504853040328045197)
              ·
                refine ⟨2625664689319890123016949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7001772504853040328045197 2625664689319890123016949)
                ·
                  refine ⟨246156064623739699032839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2625664689319890123016949 246156064623739699032839)
                  ·
                    rfl

theorem cell23_4314485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 5].length) (baseStart_4314485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314485 prefixEnd_4314485 := by exact prefixLift 4314485
  have htrace : WordTrace (prefixWord ++ tailWord_4314485) baseStart_4314485 baseEnd_4314485 := by
    simpa [prefixWord, tailWord_4314485, baseEnd_4314485] using wordTrace_append hprefix tailTrace_4314485
  have hstable : (prefixWord ++ tailWord_4314485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314485).length < 2 ^ (prefixWord ++ tailWord_4314485).sum := by decide
  have hdescent : baseEnd_4314485 < baseStart_4314485 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314498 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_4314498 : Nat := 118140960795 + 4314498 * 2 ^ 59
def prefixEnd_4314498 : Nat := 4983230072969 + 3 ^ 40 * 4314498 * 2
def baseEnd_4314498 : Nat := 738470418954055246810997

theorem tailTrace_4314498 : CollatzResearch.WordTrace tailWord_4314498 prefixEnd_4314498 738470418954055246810997 := by
  unfold tailWord_4314498
  simp only [CollatzResearch.WordTrace]
  refine ⟨39340667480829519609820037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104908446615545385626186765 39340667480829519609820037)
  ·
    refine ⟨7376375152655534926841257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39340667480829519609820037 7376375152655534926841257)
    ·
      refine ⟨5532281364491651195130943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7376375152655534926841257 5532281364491651195130943)
      ·
        refine ⟨8298422046737476792696415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5532281364491651195130943 8298422046737476792696415)
        ·
          refine ⟨12447633070106215189044623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8298422046737476792696415 12447633070106215189044623)
          ·
            refine ⟨18671449605159322783566935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12447633070106215189044623 18671449605159322783566935)
            ·
              refine ⟨28007174407738984175350403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18671449605159322783566935 28007174407738984175350403)
              ·
                refine ⟨42010761611608476263025605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28007174407738984175350403 42010761611608476263025605)
                ·
                  refine ⟨7877017802176589299317301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42010761611608476263025605 7877017802176589299317301)
                  ·
                    refine ⟨738470418954055246810997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7877017802176589299317301 738470418954055246810997)
                    ·
                      rfl

theorem cell23_4314498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_4314498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314498 prefixEnd_4314498 := by exact prefixLift 4314498
  have htrace : WordTrace (prefixWord ++ tailWord_4314498) baseStart_4314498 baseEnd_4314498 := by
    simpa [prefixWord, tailWord_4314498, baseEnd_4314498] using wordTrace_append hprefix tailTrace_4314498
  have hstable : (prefixWord ++ tailWord_4314498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314498).length < 2 ^ (prefixWord ++ tailWord_4314498).sum := by decide
  have hdescent : baseEnd_4314498 < baseStart_4314498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314501 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 4, 4, 2]
def baseStart_4314501 : Nat := 118140960795 + 4314501 * 2 ^ 59
def prefixEnd_4314501 : Nat := 4983230072969 + 3 ^ 40 * 4314501 * 2
def baseEnd_4314501 : Nat := 2215412797304129228695477

theorem tailTrace_4314501 : CollatzResearch.WordTrace tailWord_4314501 prefixEnd_4314501 2215412797304129228695477 := by
  unfold tailWord_4314501
  simp only [CollatzResearch.WordTrace]
  refine ⟨157362779342307209951639357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104908519561538139967759571 157362779342307209951639357)
  ·
    refine ⟨59011042253365203731864759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157362779342307209951639357 59011042253365203731864759)
    ·
      refine ⟨88516563380047805597797139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59011042253365203731864759 88516563380047805597797139)
      ·
        refine ⟨132774845070071708396695709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88516563380047805597797139 132774845070071708396695709)
        ·
          refine ⟨49790566901276890648760891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132774845070071708396695709 49790566901276890648760891)
          ·
            refine ⟨74685850351915335973141337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49790566901276890648760891 74685850351915335973141337)
            ·
              refine ⟨56014387763936501979856003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74685850351915335973141337 56014387763936501979856003)
              ·
                refine ⟨84021581645904752969784005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56014387763936501979856003 84021581645904752969784005)
                ·
                  refine ⟨15754046558607141181834501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84021581645904752969784005 15754046558607141181834501)
                  ·
                    refine ⟨2953883729738838971593969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15754046558607141181834501 2953883729738838971593969)
                    ·
                      refine ⟨2215412797304129228695477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2953883729738838971593969 2215412797304129228695477)
                      ·
                        rfl

theorem cell23_4314501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 4, 2].length) (baseStart_4314501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314501 prefixEnd_4314501 := by exact prefixLift 4314501
  have htrace : WordTrace (prefixWord ++ tailWord_4314501) baseStart_4314501 baseEnd_4314501 := by
    simpa [prefixWord, tailWord_4314501, baseEnd_4314501] using wordTrace_append hprefix tailTrace_4314501
  have hstable : (prefixWord ++ tailWord_4314501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314501).length < 2 ^ (prefixWord ++ tailWord_4314501).sum := by decide
  have hdescent : baseEnd_4314501 < baseStart_4314501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314568 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 3, 1, 3]
def baseStart_4314568 : Nat := 118140960795 + 4314568 * 2 ^ 59
def prefixEnd_4314568 : Nat := 4983230072969 + 3 ^ 40 * 4314568 * 2
def baseEnd_4314568 : Nat := 2215447200507980466557669

theorem tailTrace_4314568 : CollatzResearch.WordTrace tailWord_4314568 prefixEnd_4314568 2215447200507980466557669 := by
  unfold tailWord_4314568
  simp only [CollatzResearch.WordTrace]
  refine ⟨78682611516532240197164179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104910148688709653596218905 78682611516532240197164179)
  ·
    refine ⟨118023917274798360295746269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78682611516532240197164179 118023917274798360295746269)
    ·
      refine ⟨44258968978049385110904851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118023917274798360295746269 44258968978049385110904851)
      ·
        refine ⟨66388453467074077666357277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44258968978049385110904851 66388453467074077666357277)
        ·
          refine ⟨24895670050152779124883979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66388453467074077666357277 24895670050152779124883979)
          ·
            refine ⟨37343505075229168687325969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24895670050152779124883979 37343505075229168687325969)
            ·
              refine ⟨28007628806421876515494477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37343505075229168687325969 28007628806421876515494477)
              ·
                refine ⟨10502860802408203693310429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28007628806421876515494477 10502860802408203693310429)
                ·
                  refine ⟨3938572800903076384991411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10502860802408203693310429 3938572800903076384991411)
                  ·
                    refine ⟨5907859201354614577487117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3938572800903076384991411 5907859201354614577487117)
                    ·
                      refine ⟨2215447200507980466557669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5907859201354614577487117 2215447200507980466557669)
                      ·
                        rfl

theorem cell23_4314568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_4314568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314568 prefixEnd_4314568 := by exact prefixLift 4314568
  have htrace : WordTrace (prefixWord ++ tailWord_4314568) baseStart_4314568 baseEnd_4314568 := by
    simpa [prefixWord, tailWord_4314568, baseEnd_4314568] using wordTrace_append hprefix tailTrace_4314568
  have hstable : (prefixWord ++ tailWord_4314568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314568).length < 2 ^ (prefixWord ++ tailWord_4314568).sum := by decide
  have hdescent : baseEnd_4314568 < baseStart_4314568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314591 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 4]
def baseStart_4314591 : Nat := 118140960795 + 4314591 * 2 ^ 59
def prefixEnd_4314591 : Nat := 4983230072969 + 3 ^ 40 * 4314591 * 2
def baseEnd_4314591 : Nat := 2215459010563033876570063

theorem tailTrace_4314591 : CollatzResearch.WordTrace tailWord_4314591 prefixEnd_4314591 2215459010563033876570063 := by
  unfold tailWord_4314591
  simp only [CollatzResearch.WordTrace]
  refine ⟨157366061911981155322415627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104910707941320770214943751 157366061911981155322415627)
  ·
    refine ⟨236049092867971732983623441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157366061911981155322415627 236049092867971732983623441)
    ·
      refine ⟨177036819650978799737717581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236049092867971732983623441 177036819650978799737717581)
      ·
        refine ⟨66388807369117049901644093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177036819650978799737717581 66388807369117049901644093)
        ·
          refine ⟨24895802763418893713116535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66388807369117049901644093 24895802763418893713116535)
          ·
            refine ⟨37343704145128340569674803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24895802763418893713116535 37343704145128340569674803)
            ·
              refine ⟨56015556217692510854512205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37343704145128340569674803 56015556217692510854512205)
              ·
                refine ⟨21005833581634691570442077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56015556217692510854512205 21005833581634691570442077)
                ·
                  refine ⟨7877187593113009338915779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21005833581634691570442077 7877187593113009338915779)
                  ·
                    refine ⟨11815781389669514008373669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7877187593113009338915779 11815781389669514008373669)
                    ·
                      refine ⟨2215459010563033876570063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11815781389669514008373669 2215459010563033876570063)
                      ·
                        rfl

theorem cell23_4314591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_4314591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314591 prefixEnd_4314591 := by exact prefixLift 4314591
  have htrace : WordTrace (prefixWord ++ tailWord_4314591) baseStart_4314591 baseEnd_4314591 := by
    simpa [prefixWord, tailWord_4314591, baseEnd_4314591] using wordTrace_append hprefix tailTrace_4314591
  have hstable : (prefixWord ++ tailWord_4314591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314591).length < 2 ^ (prefixWord ++ tailWord_4314591).sum := by decide
  have hdescent : baseEnd_4314591 < baseStart_4314591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314595 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 2, 3, 2]
def baseStart_4314595 : Nat := 118140960795 + 4314595 * 2 ^ 59
def prefixEnd_4314595 : Nat := 4983230072969 + 3 ^ 40 * 4314595 * 2
def baseEnd_4314595 : Nat := 2215461064485651860920045

theorem tailTrace_4314595 : CollatzResearch.WordTrace tailWord_4314595 prefixEnd_4314595 2215461064485651860920045 := by
  unfold tailWord_4314595
  simp only [CollatzResearch.WordTrace]
  refine ⟨157366207803966664005561239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104910805202644442670374159 157366207803966664005561239)
  ·
    refine ⟨236049311705949996008341859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157366207803966664005561239 236049311705949996008341859)
    ·
      refine ⟨354073967558924994012512789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236049311705949996008341859 354073967558924994012512789)
      ·
        refine ⟨16597217229324609094336537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 354073967558924994012512789 16597217229324609094336537)
        ·
          refine ⟨12447912921993456820752403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16597217229324609094336537 12447912921993456820752403)
          ·
            refine ⟨18671869382990185231128605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12447912921993456820752403 18671869382990185231128605)
            ·
              refine ⟨7001951018621319461673227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18671869382990185231128605 7001951018621319461673227)
              ·
                refine ⟨10502926527931979192509841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7001951018621319461673227 10502926527931979192509841)
                ·
                  refine ⟨7877194895948984394382381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10502926527931979192509841 7877194895948984394382381)
                  ·
                    refine ⟨2953948085980869147893393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7877194895948984394382381 2953948085980869147893393)
                    ·
                      refine ⟨2215461064485651860920045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2953948085980869147893393 2215461064485651860920045)
                      ·
                        rfl

theorem cell23_4314595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_4314595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314595 prefixEnd_4314595 := by exact prefixLift 4314595
  have htrace : WordTrace (prefixWord ++ tailWord_4314595) baseStart_4314595 baseEnd_4314595 := by
    simpa [prefixWord, tailWord_4314595, baseEnd_4314595] using wordTrace_append hprefix tailTrace_4314595
  have hstable : (prefixWord ++ tailWord_4314595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314595).length < 2 ^ (prefixWord ++ tailWord_4314595).sum := by decide
  have hdescent : baseEnd_4314595 < baseStart_4314595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314605 : List Nat := [1, 5, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_4314605 : Nat := 118140960795 + 4314605 * 2 ^ 59
def prefixEnd_4314605 : Nat := 4983230072969 + 3 ^ 40 * 4314605 * 2
def baseEnd_4314605 : Nat := 738488733097398940598333

theorem tailTrace_4314605 : CollatzResearch.WordTrace tailWord_4314605 prefixEnd_4314605 738488733097398940598333 := by
  unfold tailWord_4314605
  simp only [CollatzResearch.WordTrace]
  refine ⟨157366572533930435713425269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104911048355953623808950179 157366572533930435713425269)
  ·
    refine ⟨14753116175055978348133619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157366572533930435713425269 14753116175055978348133619)
    ·
      refine ⟨22129674262583967522200429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14753116175055978348133619 22129674262583967522200429)
      ·
        refine ⟨8298627848468987820825161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22129674262583967522200429 8298627848468987820825161)
        ·
          refine ⟨6223970886351740865618871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8298627848468987820825161 6223970886351740865618871)
          ·
            refine ⟨9335956329527611298428307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6223970886351740865618871 9335956329527611298428307)
            ·
              refine ⟨14003934494291416947642461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9335956329527611298428307 14003934494291416947642461)
              ·
                refine ⟨5251475435359281355365923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14003934494291416947642461 5251475435359281355365923)
                ·
                  refine ⟨7877213153038922033048885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5251475435359281355365923 7877213153038922033048885)
                  ·
                    refine ⟨738488733097398940598333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7877213153038922033048885 738488733097398940598333)
                    ·
                      rfl

theorem cell23_4314605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_4314605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314605 prefixEnd_4314605 := by exact prefixLift 4314605
  have htrace : WordTrace (prefixWord ++ tailWord_4314605) baseStart_4314605 baseEnd_4314605 := by
    simpa [prefixWord, tailWord_4314605, baseEnd_4314605] using wordTrace_append hprefix tailTrace_4314605
  have hstable : (prefixWord ++ tailWord_4314605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314605).length < 2 ^ (prefixWord ++ tailWord_4314605).sum := by decide
  have hdescent : baseEnd_4314605 < baseStart_4314605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314608 : List Nat := [2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 4]
def baseStart_4314608 : Nat := 118140960795 + 4314608 * 2 ^ 59
def prefixEnd_4314608 : Nat := 4983230072969 + 3 ^ 40 * 4314608 * 2
def baseEnd_4314608 : Nat := 2215467739734160310057485

theorem tailTrace_4314608 : CollatzResearch.WordTrace tailWord_4314608 prefixEnd_4314608 2215467739734160310057485 := by
  unfold tailWord_4314608
  simp only [CollatzResearch.WordTrace]
  refine ⟨78683340976459783612892239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104911121301946378150522985 78683340976459783612892239)
  ·
    refine ⟨118025011464689675419338359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78683340976459783612892239 118025011464689675419338359)
    ·
      refine ⟨177037517197034513129007539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118025011464689675419338359 177037517197034513129007539)
      ·
        refine ⟨265556275795551769693511309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177037517197034513129007539 265556275795551769693511309)
        ·
          refine ⟨99583603423331913635066741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 265556275795551769693511309 99583603423331913635066741)
          ·
            refine ⟨9335962820937366903287507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99583603423331913635066741 9335962820937366903287507)
            ·
              refine ⟨14003944231406050354931261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9335962820937366903287507 14003944231406050354931261)
              ·
                refine ⟨5251479086777268883099223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14003944231406050354931261 5251479086777268883099223)
                ·
                  refine ⟨7877218630165903324648835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5251479086777268883099223 7877218630165903324648835)
                  ·
                    refine ⟨11815827945248854986973253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7877218630165903324648835 11815827945248854986973253)
                    ·
                      refine ⟨2215467739734160310057485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11815827945248854986973253 2215467739734160310057485)
                      ·
                        rfl

theorem cell23_4314608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 4].length) (baseStart_4314608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314608 prefixEnd_4314608 := by exact prefixLift 4314608
  have htrace : WordTrace (prefixWord ++ tailWord_4314608) baseStart_4314608 baseEnd_4314608 := by
    simpa [prefixWord, tailWord_4314608, baseEnd_4314608] using wordTrace_append hprefix tailTrace_4314608
  have hstable : (prefixWord ++ tailWord_4314608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314608).length < 2 ^ (prefixWord ++ tailWord_4314608).sum := by decide
  have hdescent : baseEnd_4314608 < baseStart_4314608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314611 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 3]
def baseStart_4314611 : Nat := 118140960795 + 4314611 * 2 ^ 59
def prefixEnd_4314611 : Nat := 4983230072969 + 3 ^ 40 * 4314611 * 2
def baseEnd_4314611 : Nat := 2215469280176123798319971

theorem tailTrace_4314611 : CollatzResearch.WordTrace tailWord_4314611 prefixEnd_4314611 2215469280176123798319971 := by
  unfold tailWord_4314611
  simp only [CollatzResearch.WordTrace]
  refine ⟨157366791371908698738143687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104911194247939132492095791 157366791371908698738143687)
  ·
    refine ⟨236050187057863048107215531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157366791371908698738143687 236050187057863048107215531)
    ·
      refine ⟨354075280586794572160823297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236050187057863048107215531 354075280586794572160823297)
      ·
        refine ⟨265556460440095929120617473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354075280586794572160823297 265556460440095929120617473)
        ·
          refine ⟨199167345330071946840463105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265556460440095929120617473 199167345330071946840463105)
          ·
            refine ⟨149375508997553960130347329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199167345330071946840463105 149375508997553960130347329)
            ·
              refine ⟨112031631748165470097760497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149375508997553960130347329 112031631748165470097760497)
              ·
                refine ⟨84023723811124102573320373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112031631748165470097760497 84023723811124102573320373)
                ·
                  refine ⟨7877224107292884616248785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84023723811124102573320373 7877224107292884616248785)
                  ·
                    refine ⟨5907918080469663462186589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7877224107292884616248785 5907918080469663462186589)
                    ·
                      refine ⟨2215469280176123798319971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5907918080469663462186589 2215469280176123798319971)
                      ·
                        rfl

theorem cell23_4314611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 5, 2, 3].length) (baseStart_4314611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314611 prefixEnd_4314611 := by exact prefixLift 4314611
  have htrace : WordTrace (prefixWord ++ tailWord_4314611) baseStart_4314611 baseEnd_4314611 := by
    simpa [prefixWord, tailWord_4314611, baseEnd_4314611] using wordTrace_append hprefix tailTrace_4314611
  have hstable : (prefixWord ++ tailWord_4314611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314611).length < 2 ^ (prefixWord ++ tailWord_4314611).sum := by decide
  have hdescent : baseEnd_4314611 < baseStart_4314611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314635 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 1, 6]
def baseStart_4314635 : Nat := 118140960795 + 4314635 * 2 ^ 59
def prefixEnd_4314635 : Nat := 4983230072969 + 3 ^ 40 * 4314635 * 2
def baseEnd_4314635 : Nat := 738493867903943901473287

theorem tailTrace_4314635 : CollatzResearch.WordTrace tailWord_4314635 prefixEnd_4314635 738493867903943901473287 := by
  unfold tailWord_4314635
  simp only [CollatzResearch.WordTrace]
  refine ⟨157367666723821750837017359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104911777815881167224678239 157367666723821750837017359)
  ·
    refine ⟨236051500085732626255526039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157367666723821750837017359 236051500085732626255526039)
    ·
      refine ⟨354077250128598939383289059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236051500085732626255526039 354077250128598939383289059)
      ·
        refine ⟨531115875192898409074933589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354077250128598939383289059 531115875192898409074933589)
        ·
          refine ⟨3112007081208389115673439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 531115875192898409074933589 3112007081208389115673439)
          ·
            refine ⟨4668010621812583673510159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3112007081208389115673439 4668010621812583673510159)
            ·
              refine ⟨7002015932718875510265239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4668010621812583673510159 7002015932718875510265239)
              ·
                refine ⟨10503023899078313265397859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7002015932718875510265239 10503023899078313265397859)
                ·
                  refine ⟨15754535848617469898096789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10503023899078313265397859 15754535848617469898096789)
                  ·
                    refine ⟨738493867903943901473287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15754535848617469898096789 738493867903943901473287)
                    ·
                      rfl

theorem cell23_4314635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 6].length) (baseStart_4314635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314635 prefixEnd_4314635 := by exact prefixLift 4314635
  have htrace : WordTrace (prefixWord ++ tailWord_4314635) baseStart_4314635 baseEnd_4314635 := by
    simpa [prefixWord, tailWord_4314635, baseEnd_4314635] using wordTrace_append hprefix tailTrace_4314635
  have hstable : (prefixWord ++ tailWord_4314635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314635).length < 2 ^ (prefixWord ++ tailWord_4314635).sum := by decide
  have hdescent : baseEnd_4314635 < baseStart_4314635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314638 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6]
def baseStart_4314638 : Nat := 118140960795 + 4314638 * 2 ^ 59
def prefixEnd_4314638 : Nat := 4983230072969 + 3 ^ 40 * 4314638 * 2
def baseEnd_4314638 : Nat := 2215483144153795192682347

theorem tailTrace_4314638 : CollatzResearch.WordTrace tailWord_4314638 prefixEnd_4314638 2215483144153795192682347 := by
  unfold tailWord_4314638
  simp only [CollatzResearch.WordTrace]
  refine ⟨19670972017851360293672071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104911850761873921566251045 19670972017851360293672071)
  ·
    refine ⟨29506458026777040440508107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19670972017851360293672071 29506458026777040440508107)
    ·
      refine ⟨44259687040165560660762161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29506458026777040440508107 44259687040165560660762161)
      ·
        refine ⟨33194765280124170495571621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44259687040165560660762161 33194765280124170495571621)
        ·
          refine ⟨6224018490023281967919679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33194765280124170495571621 6224018490023281967919679)
          ·
            refine ⟨9336027735034922951879519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6224018490023281967919679 9336027735034922951879519)
            ·
              refine ⟨14004041602552384427819279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9336027735034922951879519 14004041602552384427819279)
              ·
                refine ⟨21006062403828576641728919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14004041602552384427819279 21006062403828576641728919)
                ·
                  refine ⟨31509093605742864962593379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21006062403828576641728919 31509093605742864962593379)
                  ·
                    refine ⟨47263640408614297443890069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31509093605742864962593379 47263640408614297443890069)
                    ·
                      refine ⟨2215483144153795192682347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47263640408614297443890069 2215483144153795192682347)
                      ·
                        rfl

theorem cell23_4314638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_4314638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314638 prefixEnd_4314638 := by exact prefixLift 4314638
  have htrace : WordTrace (prefixWord ++ tailWord_4314638) baseStart_4314638 baseEnd_4314638 := by
    simpa [prefixWord, tailWord_4314638, baseEnd_4314638] using wordTrace_append hprefix tailTrace_4314638
  have hstable : (prefixWord ++ tailWord_4314638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314638).length < 2 ^ (prefixWord ++ tailWord_4314638).sum := by decide
  have hdescent : baseEnd_4314638 < baseStart_4314638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314645 : List Nat := [1, 3, 2, 1, 3, 3, 2, 2, 1, 2, 3]
def baseStart_4314645 : Nat := 118140960795 + 4314645 * 2 ^ 59
def prefixEnd_4314645 : Nat := 4983230072969 + 3 ^ 40 * 4314645 * 2
def baseEnd_4314645 : Nat := 2215486738518376665294815

theorem tailTrace_4314645 : CollatzResearch.WordTrace tailWord_4314645 prefixEnd_4314645 2215486738518376665294815 := by
  unfold tailWord_4314645
  simp only [CollatzResearch.WordTrace]
  refine ⟨157368031453785522544881389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104912020969190348363254259 157368031453785522544881389)
  ·
    refine ⟨59013011795169570954330521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157368031453785522544881389 59013011795169570954330521)
    ·
      refine ⟨44259758846377178215747891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59013011795169570954330521 44259758846377178215747891)
      ·
        refine ⟨66389638269565767323621837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44259758846377178215747891 66389638269565767323621837)
        ·
          refine ⟨24896114351087162746358189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66389638269565767323621837 24896114351087162746358189)
          ·
            refine ⟨9336042881657686029884321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24896114351087162746358189 9336042881657686029884321)
            ·
              refine ⟨7002032161243264522413241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9336042881657686029884321 7002032161243264522413241)
              ·
                refine ⟨5251524120932448391809931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7002032161243264522413241 5251524120932448391809931)
                ·
                  refine ⟨7877286181398672587714897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5251524120932448391809931 7877286181398672587714897)
                  ·
                    refine ⟨5907964636049004440786173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7877286181398672587714897 5907964636049004440786173)
                    ·
                      refine ⟨2215486738518376665294815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5907964636049004440786173 2215486738518376665294815)
                      ·
                        rfl

theorem cell23_4314645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_4314645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314645 prefixEnd_4314645 := by exact prefixLift 4314645
  have htrace : WordTrace (prefixWord ++ tailWord_4314645) baseStart_4314645 baseEnd_4314645 := by
    simpa [prefixWord, tailWord_4314645, baseEnd_4314645] using wordTrace_append hprefix tailTrace_4314645
  have hstable : (prefixWord ++ tailWord_4314645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314645).length < 2 ^ (prefixWord ++ tailWord_4314645).sum := by decide
  have hdescent : baseEnd_4314645 < baseStart_4314645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314658 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_4314658 : Nat := 118140960795 + 4314658 * 2 ^ 59
def prefixEnd_4314658 : Nat := 4983230072969 + 3 ^ 40 * 4314658 * 2
def baseEnd_4314658 : Nat := 2215493413766885114432255

theorem tailTrace_4314658 : CollatzResearch.WordTrace tailWord_4314658 prefixEnd_4314658 2215493413766885114432255 := by
  unfold tailWord_4314658
  simp only [CollatzResearch.WordTrace]
  refine ⟨39342126400684606441276157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104912337068492283843403085 39342126400684606441276157)
  ·
    refine ⟨14753297400256727415478559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39342126400684606441276157 14753297400256727415478559)
    ·
      refine ⟨22129946100385091123217839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14753297400256727415478559 22129946100385091123217839)
      ·
        refine ⟨33194919150577636684826759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22129946100385091123217839 33194919150577636684826759)
        ·
          refine ⟨49792378725866455027240139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33194919150577636684826759 49792378725866455027240139)
          ·
            refine ⟨74688568088799682540860209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49792378725866455027240139 74688568088799682540860209)
            ·
              refine ⟨56016426066599761905645157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74688568088799682540860209 56016426066599761905645157)
              ·
                refine ⟨10503079887487455357308467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56016426066599761905645157 10503079887487455357308467)
                ·
                  refine ⟨15754619831231183035962701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10503079887487455357308467 15754619831231183035962701)
                  ·
                    refine ⟨5907982436711693638486013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15754619831231183035962701 5907982436711693638486013)
                    ·
                      refine ⟨2215493413766885114432255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5907982436711693638486013 2215493413766885114432255)
                      ·
                        rfl

theorem cell23_4314658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_4314658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314658 prefixEnd_4314658 := by exact prefixLift 4314658
  have htrace : WordTrace (prefixWord ++ tailWord_4314658) baseStart_4314658 baseEnd_4314658 := by
    simpa [prefixWord, tailWord_4314658, baseEnd_4314658] using wordTrace_append hprefix tailTrace_4314658
  have hstable : (prefixWord ++ tailWord_4314658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314658).length < 2 ^ (prefixWord ++ tailWord_4314658).sum := by decide
  have hdescent : baseEnd_4314658 < baseStart_4314658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314668 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 7, 3, 2]
def baseStart_4314668 : Nat := 118140960795 + 4314668 * 2 ^ 59
def prefixEnd_4314668 : Nat := 4983230072969 + 3 ^ 40 * 4314668 * 2
def baseEnd_4314668 : Nat := 2215498548573430075307209

theorem tailTrace_4314668 : CollatzResearch.WordTrace tailWord_4314668 prefixEnd_4314668 2215498548573430075307209 := by
  unfold tailWord_4314668
  simp only [CollatzResearch.WordTrace]
  refine ⟨78684435166351098736484329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104912580221801464981979105 78684435166351098736484329)
  ·
    refine ⟨59013326374763324052363247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78684435166351098736484329 59013326374763324052363247)
    ·
      refine ⟨88519989562144986078544871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59013326374763324052363247 88519989562144986078544871)
      ·
        refine ⟨132779984343217479117817307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88519989562144986078544871 132779984343217479117817307)
        ·
          refine ⟨199169976514826218676725961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132779984343217479117817307 199169976514826218676725961)
          ·
            refine ⟨149377482386119664007544471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199169976514826218676725961 149377482386119664007544471)
            ·
              refine ⟨224066223579179496011316707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149377482386119664007544471 224066223579179496011316707)
              ·
                refine ⟨336099335368769244016975061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224066223579179496011316707 336099335368769244016975061)
                ·
                  refine ⟨7877328172705529156647853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 336099335368769244016975061 7877328172705529156647853)
                  ·
                    refine ⟨2953998064764573433742945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7877328172705529156647853 2953998064764573433742945)
                    ·
                      refine ⟨2215498548573430075307209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2953998064764573433742945 2215498548573430075307209)
                      ·
                        rfl

theorem cell23_4314668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 3, 2].length) (baseStart_4314668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314668 prefixEnd_4314668 := by exact prefixLift 4314668
  have htrace : WordTrace (prefixWord ++ tailWord_4314668) baseStart_4314668 baseEnd_4314668 := by
    simpa [prefixWord, tailWord_4314668, baseEnd_4314668] using wordTrace_append hprefix tailTrace_4314668
  have hstable : (prefixWord ++ tailWord_4314668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314668).length < 2 ^ (prefixWord ++ tailWord_4314668).sum := by decide
  have hdescent : baseEnd_4314668 < baseStart_4314668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314761 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 7]
def baseStart_4314761 : Nat := 118140960795 + 4314761 * 2 ^ 59
def prefixEnd_4314761 : Nat := 4983230072969 + 3 ^ 40 * 4314761 * 2
def baseEnd_4314761 : Nat := 2215546302274298211444281

theorem tailTrace_4314761 : CollatzResearch.WordTrace tailWord_4314761 prefixEnd_4314761 2215546302274298211444281 := by
  unfold tailWord_4314761
  simp only [CollatzResearch.WordTrace]
  refine ⟨157372262321365274356104137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104914841547576849570736091 157372262321365274356104137)
  ·
    refine ⟨118029196741023955767078103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157372262321365274356104137 118029196741023955767078103)
    ·
      refine ⟨177043795111535933650617155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118029196741023955767078103 177043795111535933650617155)
      ·
        refine ⟨265565692667303900475925733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177043795111535933650617155 265565692667303900475925733)
        ·
          refine ⟨49793567375119481339236075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 265565692667303900475925733 49793567375119481339236075)
          ·
            refine ⟨74690351062679222008854113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49793567375119481339236075 74690351062679222008854113)
            ·
              refine ⟨56017763297009416506640585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74690351062679222008854113 56017763297009416506640585)
              ·
                refine ⟨42013322472757062379980439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56017763297009416506640585 42013322472757062379980439)
                ·
                  refine ⟨63019983709135593569970659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42013322472757062379980439 63019983709135593569970659)
                  ·
                    refine ⟨94529975563703390354955989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63019983709135593569970659 94529975563703390354955989)
                    ·
                      refine ⟨2215546302274298211444281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94529975563703390354955989 2215546302274298211444281)
                      ·
                        rfl

theorem cell23_4314761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 1, 1, 7].length) (baseStart_4314761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314761 prefixEnd_4314761 := by exact prefixLift 4314761
  have htrace : WordTrace (prefixWord ++ tailWord_4314761) baseStart_4314761 baseEnd_4314761 := by
    simpa [prefixWord, tailWord_4314761, baseEnd_4314761] using wordTrace_append hprefix tailTrace_4314761
  have hstable : (prefixWord ++ tailWord_4314761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314761).length < 2 ^ (prefixWord ++ tailWord_4314761).sum := by decide
  have hdescent : baseEnd_4314761 < baseStart_4314761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314783 : List Nat := [1, 1, 2, 7, 2, 1, 1, 2, 2, 2, 2]
def baseStart_4314783 : Nat := 118140960795 + 4314783 * 2 ^ 59
def prefixEnd_4314783 : Nat := 4983230072969 + 3 ^ 40 * 4314783 * 2
def baseEnd_4314783 : Nat := 2215557598848697125369181

theorem tailTrace_4314783 : CollatzResearch.WordTrace tailWord_4314783 prefixEnd_4314783 2215557598848697125369181 := by
  unfold tailWord_4314783
  simp only [CollatzResearch.WordTrace]
  refine ⟨157373064727285572113405003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104915376484857048075603335 157373064727285572113405003)
  ·
    refine ⟨236059597090928358170107505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157373064727285572113405003 236059597090928358170107505)
    ·
      refine ⟨177044697818196268627580629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236059597090928358170107505 177044697818196268627580629)
      ·
        refine ⟨4149485105113975045958921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 177044697818196268627580629 4149485105113975045958921)
        ·
          refine ⟨3112113828835481284469191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4149485105113975045958921 3112113828835481284469191)
          ·
            refine ⟨4668170743253221926703787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3112113828835481284469191 4668170743253221926703787)
            ·
              refine ⟨7002256114879832890055681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4668170743253221926703787 7002256114879832890055681)
              ·
                refine ⟨5251692086159874667541761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7002256114879832890055681 5251692086159874667541761)
                ·
                  refine ⟨3938769064619906000656321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5251692086159874667541761 3938769064619906000656321)
                  ·
                    refine ⟨2954076798464929500492241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3938769064619906000656321 2954076798464929500492241)
                    ·
                      refine ⟨2215557598848697125369181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2954076798464929500492241 2215557598848697125369181)
                      ·
                        rfl

theorem cell23_4314783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_4314783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314783 prefixEnd_4314783 := by exact prefixLift 4314783
  have htrace : WordTrace (prefixWord ++ tailWord_4314783) baseStart_4314783 baseEnd_4314783 := by
    simpa [prefixWord, tailWord_4314783, baseEnd_4314783] using wordTrace_append hprefix tailTrace_4314783
  have hstable : (prefixWord ++ tailWord_4314783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314783).length < 2 ^ (prefixWord ++ tailWord_4314783).sum := by decide
  have hdescent : baseEnd_4314783 < baseStart_4314783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314849 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 3, 4]
def baseStart_4314849 : Nat := 118140960795 + 4314849 * 2 ^ 59
def prefixEnd_4314849 : Nat := 4983230072969 + 3 ^ 40 * 4314849 * 2
def baseEnd_4314849 : Nat := 738530496190631289047959

theorem tailTrace_4314849 : CollatzResearch.WordTrace tailWord_4314849 prefixEnd_4314849 738530496190631289047959 := by
  unfold tailWord_4314849
  simp only [CollatzResearch.WordTrace]
  refine ⟨157375471945046465385307601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104916981296697643590205067 157375471945046465385307601)
  ·
    refine ⟨118031603958784849038980701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157375471945046465385307601 118031603958784849038980701)
    ·
      refine ⟨44261851484544318389617763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118031603958784849038980701 44261851484544318389617763)
      ·
        refine ⟨66392777226816477584426645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44261851484544318389617763 66392777226816477584426645)
        ·
          refine ⟨3112161432507022386769999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 66392777226816477584426645 3112161432507022386769999)
          ·
            refine ⟨4668242148760533580154999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3112161432507022386769999 4668242148760533580154999)
            ·
              refine ⟨7002363223140800370232499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4668242148760533580154999 7002363223140800370232499)
              ·
                refine ⟨10503544834711200555348749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7002363223140800370232499 10503544834711200555348749)
                ·
                  refine ⟨3938829313016700208255781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10503544834711200555348749 3938829313016700208255781)
                  ·
                    refine ⟨738530496190631289047959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3938829313016700208255781 738530496190631289047959)
                    ·
                      rfl

theorem cell23_4314849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_4314849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314849 prefixEnd_4314849 := by exact prefixLift 4314849
  have htrace : WordTrace (prefixWord ++ tailWord_4314849) baseStart_4314849 baseEnd_4314849 := by
    simpa [prefixWord, tailWord_4314849, baseEnd_4314849] using wordTrace_append hprefix tailTrace_4314849
  have hstable : (prefixWord ++ tailWord_4314849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314849).length < 2 ^ (prefixWord ++ tailWord_4314849).sum := by decide
  have hdescent : baseEnd_4314849 < baseStart_4314849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314906 : List Nat := [3, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3]
def baseStart_4314906 : Nat := 118140960795 + 4314906 * 2 ^ 59
def prefixEnd_4314906 : Nat := 4983230072969 + 3 ^ 40 * 4314906 * 2
def baseEnd_4314906 : Nat := 2215620756969200144131115

theorem tailTrace_4314906 : CollatzResearch.WordTrace tailWord_4314906 prefixEnd_4314906 2215620756969200144131115 := by
  unfold tailWord_4314906
  simp only [CollatzResearch.WordTrace]
  refine ⟨39344387726459991030033143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104918367270559976080088381 39344387726459991030033143)
  ·
    refine ⟨59016581589689986545049715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39344387726459991030033143 59016581589689986545049715)
    ·
      refine ⟨88524872384534979817574573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59016581589689986545049715 88524872384534979817574573)
      ·
        refine ⟨33196827144200617431590465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88524872384534979817574573 33196827144200617431590465)
        ·
          refine ⟨24897620358150463073692849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33196827144200617431590465 24897620358150463073692849)
          ·
            refine ⟨18673215268612847305269637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24897620358150463073692849 18673215268612847305269637)
            ·
              refine ⟨3501227862864908869738057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18673215268612847305269637 3501227862864908869738057)
              ·
                refine ⟨2625920897148681652303543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3501227862864908869738057 2625920897148681652303543)
                ·
                  refine ⟨3938881345723022478455315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2625920897148681652303543 3938881345723022478455315)
                  ·
                    refine ⟨5908322018584533717682973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3938881345723022478455315 5908322018584533717682973)
                    ·
                      refine ⟨2215620756969200144131115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5908322018584533717682973 2215620756969200144131115)
                      ·
                        rfl

theorem cell23_4314906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_4314906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314906 prefixEnd_4314906 := by exact prefixLift 4314906
  have htrace : WordTrace (prefixWord ++ tailWord_4314906) baseStart_4314906 baseEnd_4314906 := by
    simpa [prefixWord, tailWord_4314906, baseEnd_4314906] using wordTrace_append hprefix tailTrace_4314906
  have hstable : (prefixWord ++ tailWord_4314906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314906).length < 2 ^ (prefixWord ++ tailWord_4314906).sum := by decide
  have hdescent : baseEnd_4314906 < baseStart_4314906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314915 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 3]
def baseStart_4314915 : Nat := 118140960795 + 4314915 * 2 ^ 59
def prefixEnd_4314915 : Nat := 4983230072969 + 3 ^ 40 * 4314915 * 2
def baseEnd_4314915 : Nat := 2215625378295090608918573

theorem tailTrace_4314915 : CollatzResearch.WordTrace tailWord_4314915 prefixEnd_4314915 2215625378295090608918573 := by
  unfold tailWord_4314915
  simp only [CollatzResearch.WordTrace]
  refine ⟨157377879162807358657210199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104918586108538239104806799 157377879162807358657210199)
  ·
    refine ⟨236066818744211037985815299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157377879162807358657210199 236066818744211037985815299)
    ·
      refine ⟨354100228116316556978722949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236066818744211037985815299 354100228116316556978722949)
      ·
        refine ⟨66393792771809354433510553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 354100228116316556978722949 66393792771809354433510553)
        ·
          refine ⟨49795344578857015825132915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66393792771809354433510553 49795344578857015825132915)
          ·
            refine ⟨74693016868285523737699373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49795344578857015825132915 74693016868285523737699373)
            ·
              refine ⟨28009881325607071401637265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74693016868285523737699373 28009881325607071401637265)
              ·
                refine ⟨21007410994205303551227949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28009881325607071401637265 21007410994205303551227949)
                ·
                  refine ⟨7877779122826988831710481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21007410994205303551227949 7877779122826988831710481)
                  ·
                    refine ⟨5908334342120241623782861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7877779122826988831710481 5908334342120241623782861)
                    ·
                      refine ⟨2215625378295090608918573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5908334342120241623782861 2215625378295090608918573)
                      ·
                        rfl

theorem cell23_4314915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_4314915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314915 prefixEnd_4314915 := by exact prefixLift 4314915
  have htrace : WordTrace (prefixWord ++ tailWord_4314915) baseStart_4314915 baseEnd_4314915 := by
    simpa [prefixWord, tailWord_4314915, baseEnd_4314915] using wordTrace_append hprefix tailTrace_4314915
  have hstable : (prefixWord ++ tailWord_4314915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314915).length < 2 ^ (prefixWord ++ tailWord_4314915).sum := by decide
  have hdescent : baseEnd_4314915 < baseStart_4314915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314929 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 3, 2, 2]
def baseStart_4314929 : Nat := 118140960795 + 4314929 * 2 ^ 59
def prefixEnd_4314929 : Nat := 4983230072969 + 3 ^ 40 * 4314929 * 2
def baseEnd_4314929 : Nat := 2215632567024253554143509

theorem tailTrace_4314929 : CollatzResearch.WordTrace tailWord_4314929 prefixEnd_4314929 2215632567024253554143509 := by
  unfold tailWord_4314929
  simp only [CollatzResearch.WordTrace]
  refine ⟨157378389784756639048219841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104918926523171092698813227 157378389784756639048219841)
  ·
    refine ⟨118033792338567479286164881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157378389784756639048219841 118033792338567479286164881)
    ·
      refine ⟨88525344253925609464623661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118033792338567479286164881 88525344253925609464623661)
      ·
        refine ⟨33197004095222103549233873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88525344253925609464623661 33197004095222103549233873)
        ·
          refine ⟨24897753071416577661925405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33197004095222103549233873 24897753071416577661925405)
          ·
            refine ⟨9336657401781216623222027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24897753071416577661925405 9336657401781216623222027)
            ·
              refine ⟨14004986102671824934833041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9336657401781216623222027 14004986102671824934833041)
              ·
                refine ⟨10503739577003868701124781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14004986102671824934833041 10503739577003868701124781)
                ·
                  refine ⟨3938902341376450762921793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10503739577003868701124781 3938902341376450762921793)
                  ·
                    refine ⟨2954176756032338072191345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3938902341376450762921793 2954176756032338072191345)
                    ·
                      refine ⟨2215632567024253554143509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2954176756032338072191345 2215632567024253554143509)
                      ·
                        rfl

theorem cell23_4314929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_4314929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314929 prefixEnd_4314929 := by exact prefixLift 4314929
  have htrace : WordTrace (prefixWord ++ tailWord_4314929) baseStart_4314929 baseEnd_4314929 := by
    simpa [prefixWord, tailWord_4314929, baseEnd_4314929] using wordTrace_append hprefix tailTrace_4314929
  have hstable : (prefixWord ++ tailWord_4314929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314929).length < 2 ^ (prefixWord ++ tailWord_4314929).sum := by decide
  have hdescent : baseEnd_4314929 < baseStart_4314929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314942 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_4314942 : Nat := 118140960795 + 4314942 * 2 ^ 59
def prefixEnd_4314942 : Nat := 4983230072969 + 3 ^ 40 * 4314942 * 2
def baseEnd_4314942 : Nat := 2215639242272762003280949

theorem tailTrace_4314942 : CollatzResearch.WordTrace tailWord_4314942 prefixEnd_4314942 2215639242272762003280949 := by
  unfold tailWord_4314942
  simp only [CollatzResearch.WordTrace]
  refine ⟨19672357991713692783555385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104919242622473028178962053 19672357991713692783555385)
  ·
    refine ⟨14754268493785269587666539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19672357991713692783555385 14754268493785269587666539)
    ·
      refine ⟨22131402740677904381499809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14754268493785269587666539 22131402740677904381499809)
      ·
        refine ⟨16598552055508428286124857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22131402740677904381499809 16598552055508428286124857)
        ·
          refine ⟨12448914041631321214593643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16598552055508428286124857 12448914041631321214593643)
          ·
            refine ⟨18673371062446981821890465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12448914041631321214593643 18673371062446981821890465)
            ·
              refine ⟨14005028296835236366417849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18673371062446981821890465 14005028296835236366417849)
              ·
                refine ⟨10503771222626427274813387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14005028296835236366417849 10503771222626427274813387)
                ·
                  refine ⟨15755656833939640912220081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10503771222626427274813387 15755656833939640912220081)
                  ·
                    refine ⟨11816742625454730684165061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15755656833939640912220081 11816742625454730684165061)
                    ·
                      refine ⟨2215639242272762003280949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11816742625454730684165061 2215639242272762003280949)
                      ·
                        rfl

theorem cell23_4314942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_4314942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314942 prefixEnd_4314942 := by exact prefixLift 4314942
  have htrace : WordTrace (prefixWord ++ tailWord_4314942) baseStart_4314942 baseEnd_4314942 := by
    simpa [prefixWord, tailWord_4314942, baseEnd_4314942] using wordTrace_append hprefix tailTrace_4314942
  have hstable : (prefixWord ++ tailWord_4314942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314942).length < 2 ^ (prefixWord ++ tailWord_4314942).sum := by decide
  have hdescent : baseEnd_4314942 < baseStart_4314942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314956 : List Nat := [2, 2, 1, 3, 5, 1, 1, 2, 2, 4]
def baseStart_4314956 : Nat := 118140960795 + 4314956 * 2 ^ 59
def prefixEnd_4314956 : Nat := 4983230072969 + 3 ^ 40 * 4314956 * 2
def baseEnd_4314956 : Nat := 738548810333974982835295

theorem tailTrace_4314956 : CollatzResearch.WordTrace tailWord_4314956 prefixEnd_4314956 738548810333974982835295 := by
  unfold tailWord_4314956
  simp only [CollatzResearch.WordTrace]
  refine ⟨78689687277829411329726361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104919583037105881772968481 78689687277829411329726361)
  ·
    refine ⟨59017265458372058497294771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78689687277829411329726361 59017265458372058497294771)
    ·
      refine ⟨88525898187558087745942157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59017265458372058497294771 88525898187558087745942157)
      ·
        refine ⟨33197211820334282904728309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88525898187558087745942157 33197211820334282904728309)
        ·
          refine ⟨3112238608156339022318279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33197211820334282904728309 3112238608156339022318279)
          ·
            refine ⟨4668357912234508533477419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3112238608156339022318279 4668357912234508533477419)
            ·
              refine ⟨7002536868351762800216129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4668357912234508533477419 7002536868351762800216129)
              ·
                refine ⟨5251902651263822100162097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7002536868351762800216129 5251902651263822100162097)
                ·
                  refine ⟨3938926988447866575121573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5251902651263822100162097 3938926988447866575121573)
                  ·
                    refine ⟨738548810333974982835295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3938926988447866575121573 738548810333974982835295)
                    ·
                      rfl

theorem cell23_4314956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_4314956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314956 prefixEnd_4314956 := by exact prefixLift 4314956
  have htrace : WordTrace (prefixWord ++ tailWord_4314956) baseStart_4314956 baseEnd_4314956 := by
    simpa [prefixWord, tailWord_4314956, baseEnd_4314956] using wordTrace_append hprefix tailTrace_4314956
  have hstable : (prefixWord ++ tailWord_4314956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314956).length < 2 ^ (prefixWord ++ tailWord_4314956).sum := by decide
  have hdescent : baseEnd_4314956 < baseStart_4314956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314979 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 1, 3, 3]
def baseStart_4314979 : Nat := 118140960795 + 4314979 * 2 ^ 59
def prefixEnd_4314979 : Nat := 4983230072969 + 3 ^ 40 * 4314979 * 2
def baseEnd_4314979 : Nat := 2215658241056978358518279

theorem tailTrace_4314979 : CollatzResearch.WordTrace tailWord_4314979 prefixEnd_4314979 2215658241056978358518279 := by
  unfold tailWord_4314979
  simp only [CollatzResearch.WordTrace]
  refine ⟨157380213434575497587539991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104920142289716998391693327 157380213434575497587539991)
  ·
    refine ⟨236070320151863246381309987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157380213434575497587539991 236070320151863246381309987)
    ·
      refine ⟨354105480227794869571964981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236070320151863246381309987 354105480227794869571964981)
      ·
        refine ⟨33197388771355769022371717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 354105480227794869571964981 33197388771355769022371717)
        ·
          refine ⟨6224510394629206691694697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33197388771355769022371717 6224510394629206691694697)
          ·
            refine ⟨4668382795971905018771023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6224510394629206691694697 4668382795971905018771023)
            ·
              refine ⟨7002574193957857528156535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4668382795971905018771023 7002574193957857528156535)
              ·
                refine ⟨10503861290936786292234803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7002574193957857528156535 10503861290936786292234803)
                ·
                  refine ⟨15755791936405179438352205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10503861290936786292234803 15755791936405179438352205)
                  ·
                    refine ⟨5908421976151942289382077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15755791936405179438352205 5908421976151942289382077)
                    ·
                      refine ⟨2215658241056978358518279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5908421976151942289382077 2215658241056978358518279)
                      ·
                        rfl

theorem cell23_4314979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_4314979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314979 prefixEnd_4314979 := by exact prefixLift 4314979
  have htrace : WordTrace (prefixWord ++ tailWord_4314979) baseStart_4314979 baseEnd_4314979 := by
    simpa [prefixWord, tailWord_4314979, baseEnd_4314979] using wordTrace_append hprefix tailTrace_4314979
  have hstable : (prefixWord ++ tailWord_4314979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314979).length < 2 ^ (prefixWord ++ tailWord_4314979).sum := by decide
  have hdescent : baseEnd_4314979 < baseStart_4314979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314986 : List Nat := [3, 1, 3, 4, 2, 1, 2, 7]
def baseStart_4314986 : Nat := 118140960795 + 4314986 * 2 ^ 59
def prefixEnd_4314986 : Nat := 4983230072969 + 3 ^ 40 * 4314986 * 2
def baseEnd_4314986 : Nat := 82061549460057771523361

theorem tailTrace_4314986 : CollatzResearch.WordTrace tailWord_4314986 prefixEnd_4314986 82061549460057771523361 := by
  unfold tailWord_4314986
  simp only [CollatzResearch.WordTrace]
  refine ⟨39345117186387534445761203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104920312497033425188696541 39345117186387534445761203)
  ·
    refine ⟨59017675779581301668641805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39345117186387534445761203 59017675779581301668641805)
    ·
      refine ⟨22131628417342988125740677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59017675779581301668641805 22131628417342988125740677)
      ·
        refine ⟨4149680328251810273576377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22131628417342988125740677 4149680328251810273576377)
        ·
          refine ⟨3112260246188857705182283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4149680328251810273576377 3112260246188857705182283)
          ·
            refine ⟨4668390369283286557773425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3112260246188857705182283 4668390369283286557773425)
            ·
              refine ⟨3501292776962464918330069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4668390369283286557773425 3501292776962464918330069)
              ·
                refine ⟨82061549460057771523361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3501292776962464918330069 82061549460057771523361)
                ·
                  rfl

theorem cell23_4314986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 7].length) (baseStart_4314986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314986 prefixEnd_4314986 := by exact prefixLift 4314986
  have htrace : WordTrace (prefixWord ++ tailWord_4314986) baseStart_4314986 baseEnd_4314986 := by
    simpa [prefixWord, tailWord_4314986, baseEnd_4314986] using wordTrace_append hprefix tailTrace_4314986
  have hstable : (prefixWord ++ tailWord_4314986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314986).length < 2 ^ (prefixWord ++ tailWord_4314986).sum := by decide
  have hdescent : baseEnd_4314986 < baseStart_4314986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4314989 : List Nat := [1, 5, 1, 1, 1, 1, 3, 4, 1, 3, 2]
def baseStart_4314989 : Nat := 118140960795 + 4314989 * 2 ^ 59
def prefixEnd_4314989 : Nat := 4983230072969 + 3 ^ 40 * 4314989 * 2
def baseEnd_4314989 : Nat := 2215663375863523319393233

theorem tailTrace_4314989 : CollatzResearch.WordTrace tailWord_4314989 prefixEnd_4314989 2215663375863523319393233 := by
  unfold tailWord_4314989
  simp only [CollatzResearch.WordTrace]
  refine ⟨157380578164539269295404021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104920385443026179530269347 157380578164539269295404021)
  ·
    refine ⟨14754429202925556496444127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157380578164539269295404021 14754429202925556496444127)
    ·
      refine ⟨22131643804388334744666191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14754429202925556496444127 22131643804388334744666191)
      ·
        refine ⟨33197465706582502116999287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22131643804388334744666191 33197465706582502116999287)
        ·
          refine ⟨49796198559873753175498931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33197465706582502116999287 49796198559873753175498931)
          ·
            refine ⟨74694297839810629763248397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49796198559873753175498931 74694297839810629763248397)
            ·
              refine ⟨28010361689928986161218149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74694297839810629763248397 28010361689928986161218149)
              ·
                refine ⟨5251942816861684905228403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28010361689928986161218149 5251942816861684905228403)
                ·
                  refine ⟨7877914225292527357842605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5251942816861684905228403 7877914225292527357842605)
                  ·
                    refine ⟨2954217834484697759190977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7877914225292527357842605 2954217834484697759190977)
                    ·
                      refine ⟨2215663375863523319393233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2954217834484697759190977 2215663375863523319393233)
                      ·
                        rfl

theorem cell23_4314989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_4314989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4314989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4314989 prefixEnd_4314989 := by exact prefixLift 4314989
  have htrace : WordTrace (prefixWord ++ tailWord_4314989) baseStart_4314989 baseEnd_4314989 := by
    simpa [prefixWord, tailWord_4314989, baseEnd_4314989] using wordTrace_append hprefix tailTrace_4314989
  have hstable : (prefixWord ++ tailWord_4314989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4314989).length < 2 ^ (prefixWord ++ tailWord_4314989).sum := by decide
  have hdescent : baseEnd_4314989 < baseStart_4314989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4314989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315002 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2]
def baseStart_4315002 : Nat := 118140960795 + 4315002 * 2 ^ 59
def prefixEnd_4315002 : Nat := 4983230072969 + 3 ^ 40 * 4315002 * 2
def baseEnd_4315002 : Nat := 2215670051112031768530673

theorem tailTrace_4315002 : CollatzResearch.WordTrace tailWord_4315002 prefixEnd_4315002 2215670051112031768530673 := by
  unfold tailWord_4315002
  simp only [CollatzResearch.WordTrace]
  refine ⟨39345263078373043128906815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104920701542328115010418173 39345263078373043128906815)
  ·
    refine ⟨59017894617559564693360223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39345263078373043128906815 59017894617559564693360223)
    ·
      refine ⟨88526841926339347040040335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59017894617559564693360223 88526841926339347040040335)
      ·
        refine ⟨132790262889509020560060503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88526841926339347040040335 132790262889509020560060503)
        ·
          refine ⟨199185394334263530840090755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132790262889509020560060503 199185394334263530840090755)
          ·
            refine ⟨298778091501395296260136133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199185394334263530840090755 298778091501395296260136133)
            ·
              refine ⟨56020892156511618048775525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 298778091501395296260136133 56020892156511618048775525)
              ·
                refine ⟨10503917279345928384145411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56020892156511618048775525 10503917279345928384145411)
                ·
                  refine ⟨15755875919018892576218117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10503917279345928384145411 15755875919018892576218117)
                  ·
                    refine ⟨2954226734816042358040897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15755875919018892576218117 2954226734816042358040897)
                    ·
                      refine ⟨2215670051112031768530673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2954226734816042358040897 2215670051112031768530673)
                      ·
                        rfl

theorem cell23_4315002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2].length) (baseStart_4315002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315002 prefixEnd_4315002 := by exact prefixLift 4315002
  have htrace : WordTrace (prefixWord ++ tailWord_4315002) baseStart_4315002 baseEnd_4315002 := by
    simpa [prefixWord, tailWord_4315002, baseEnd_4315002] using wordTrace_append hprefix tailTrace_4315002
  have hstable : (prefixWord ++ tailWord_4315002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315002).length < 2 ^ (prefixWord ++ tailWord_4315002).sum := by decide
  have hdescent : baseEnd_4315002 < baseStart_4315002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315005 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 1, 6, 3]
def baseStart_4315005 : Nat := 118140960795 + 4315005 * 2 ^ 59
def prefixEnd_4315005 : Nat := 4983230072969 + 3 ^ 40 * 4315005 * 2
def baseEnd_4315005 : Nat := 2215671591553995256793159

theorem tailTrace_4315005 : CollatzResearch.WordTrace tailWord_4315005 prefixEnd_4315005 2215671591553995256793159 := by
  unfold tailWord_4315005
  simp only [CollatzResearch.WordTrace]
  refine ⟨157381161732481304027986469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104920774488320869351990979 157381161732481304027986469)
  ·
    refine ⟨29508967824840244505247463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157381161732481304027986469 29508967824840244505247463)
    ·
      refine ⟨44263451737260366757871195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29508967824840244505247463 44263451737260366757871195)
      ·
        refine ⟨66395177605890550136806793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44263451737260366757871195 66395177605890550136806793)
        ·
          refine ⟨49796383204417912602605095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66395177605890550136806793 49796383204417912602605095)
          ·
            refine ⟨74694574806626868903907643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49796383204417912602605095 74694574806626868903907643)
            ·
              refine ⟨112041862209940303355861465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74694574806626868903907643 112041862209940303355861465)
              ·
                refine ⟨84031396657455227516896099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112041862209940303355861465 84031396657455227516896099)
                ·
                  refine ⟨126047094986182841275344149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84031396657455227516896099 126047094986182841275344149)
                  ·
                    refine ⟨5908457577477320684781757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 126047094986182841275344149 5908457577477320684781757)
                    ·
                      refine ⟨2215671591553995256793159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5908457577477320684781757 2215671591553995256793159)
                      ·
                        rfl

theorem cell23_4315005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_4315005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315005 prefixEnd_4315005 := by exact prefixLift 4315005
  have htrace : WordTrace (prefixWord ++ tailWord_4315005) baseStart_4315005 baseEnd_4315005 := by
    simpa [prefixWord, tailWord_4315005, baseEnd_4315005] using wordTrace_append hprefix tailTrace_4315005
  have hstable : (prefixWord ++ tailWord_4315005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315005).length < 2 ^ (prefixWord ++ tailWord_4315005).sum := by decide
  have hdescent : baseEnd_4315005 < baseStart_4315005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315019 : List Nat := [1, 1, 1, 1, 4, 2, 1, 6, 2, 2, 2]
def baseStart_4315019 : Nat := 118140960795 + 4315019 * 2 ^ 59
def prefixEnd_4315019 : Nat := 4983230072969 + 3 ^ 40 * 4315019 * 2
def baseEnd_4315019 : Nat := 2215678780283158202018095

theorem tailTrace_4315019 : CollatzResearch.WordTrace tailWord_4315019 prefixEnd_4315019 2215678780283158202018095 := by
  unfold tailWord_4315019
  simp only [CollatzResearch.WordTrace]
  refine ⟨157381672354430584418996111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104921114902953722945997407 157381672354430584418996111)
  ·
    refine ⟨236072508531645876628494167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157381672354430584418996111 236072508531645876628494167)
    ·
      refine ⟨354108762797468814942741251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236072508531645876628494167 354108762797468814942741251)
      ·
        refine ⟨531163144196203222414111877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354108762797468814942741251 531163144196203222414111877)
        ·
          refine ⟨99593089536788104202645977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 531163144196203222414111877 99593089536788104202645977)
          ·
            refine ⟨74694817152591078151984483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99593089536788104202645977 74694817152591078151984483)
            ·
              refine ⟨112042225728886617227976725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74694817152591078151984483 112042225728886617227976725)
              ·
                refine ⟨5251979331041560182561409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112042225728886617227976725 5251979331041560182561409)
                ·
                  refine ⟨3938984498281170136921057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5251979331041560182561409 3938984498281170136921057)
                  ·
                    refine ⟨2954238373710877602690793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3938984498281170136921057 2954238373710877602690793)
                    ·
                      refine ⟨2215678780283158202018095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2954238373710877602690793 2215678780283158202018095)
                      ·
                        rfl

theorem cell23_4315019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 2, 2, 2].length) (baseStart_4315019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315019 prefixEnd_4315019 := by exact prefixLift 4315019
  have htrace : WordTrace (prefixWord ++ tailWord_4315019) baseStart_4315019 baseEnd_4315019 := by
    simpa [prefixWord, tailWord_4315019, baseEnd_4315019] using wordTrace_append hprefix tailTrace_4315019
  have hstable : (prefixWord ++ tailWord_4315019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315019).length < 2 ^ (prefixWord ++ tailWord_4315019).sum := by decide
  have hdescent : baseEnd_4315019 < baseStart_4315019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315025 : List Nat := [1, 2, 2, 1, 1, 1, 7, 1, 7]
def baseStart_4315025 : Nat := 118140960795 + 4315025 * 2 ^ 59
def prefixEnd_4315025 : Nat := 4983230072969 + 3 ^ 40 * 4315025 * 2
def baseEnd_4315025 : Nat := 246186873463009464282563

theorem tailTrace_4315025 : CollatzResearch.WordTrace tailWord_4315025 prefixEnd_4315025 246186873463009464282563 := by
  unfold tailWord_4315025
  simp only [CollatzResearch.WordTrace]
  refine ⟨157381891192408847443714529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104921260794939231629143019 157381891192408847443714529)
  ·
    refine ⟨118036418394306635582785897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157381891192408847443714529 118036418394306635582785897)
    ·
      refine ⟨88527313795729976687089423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118036418394306635582785897 88527313795729976687089423)
      ·
        refine ⟨132790970693594965030634135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88527313795729976687089423 132790970693594965030634135)
        ·
          refine ⟨199186456040392447545951203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132790970693594965030634135 199186456040392447545951203)
          ·
            refine ⟨298779684060588671318926805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199186456040392447545951203 298779684060588671318926805)
            ·
              refine ⟨7002648845170046984037347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 298779684060588671318926805 7002648845170046984037347)
              ·
                refine ⟨10503973267755070476056021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7002648845170046984037347 10503973267755070476056021)
                ·
                  refine ⟨246186873463009464282563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10503973267755070476056021 246186873463009464282563)
                  ·
                    rfl

theorem cell23_4315025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 7].length) (baseStart_4315025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315025 prefixEnd_4315025 := by exact prefixLift 4315025
  have htrace : WordTrace (prefixWord ++ tailWord_4315025) baseStart_4315025 baseEnd_4315025 := by
    simpa [prefixWord, tailWord_4315025, baseEnd_4315025] using wordTrace_append hprefix tailTrace_4315025
  have hstable : (prefixWord ++ tailWord_4315025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315025).length < 2 ^ (prefixWord ++ tailWord_4315025).sum := by decide
  have hdescent : baseEnd_4315025 < baseStart_4315025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315030 : List Nat := [5, 3, 1, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_4315030 : Nat := 118140960795 + 4315030 * 2 ^ 59
def prefixEnd_4315030 : Nat := 4983230072969 + 3 ^ 40 * 4315030 * 2
def baseEnd_4315030 : Nat := 2215684428570357658980545

theorem tailTrace_4315030 : CollatzResearch.WordTrace tailWord_4315030 prefixEnd_4315030 2215684428570357658980545 := by
  unfold tailWord_4315030
  simp only [CollatzResearch.WordTrace]
  refine ⟨9836379597336920831102909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 104921382371593822198431029 9836379597336920831102909)
  ·
    refine ⟨3688642349001345311663591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9836379597336920831102909 3688642349001345311663591)
    ·
      refine ⟨5532963523502017967495387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3688642349001345311663591 5532963523502017967495387)
      ·
        refine ⟨8299445285253026951243081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5532963523502017967495387 8299445285253026951243081)
        ·
          refine ⟨6224583963939770213432311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8299445285253026951243081 6224583963939770213432311)
          ·
            refine ⟨9336875945909655320148467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6224583963939770213432311 9336875945909655320148467)
            ·
              refine ⟨14005313918864482980222701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9336875945909655320148467 14005313918864482980222701)
              ·
                refine ⟨5251992719574181117583513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14005313918864482980222701 5251992719574181117583513)
                ·
                  refine ⟨3938994539680635838187635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5251992719574181117583513 3938994539680635838187635)
                  ·
                    refine ⟨5908491809520953757281453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3938994539680635838187635 5908491809520953757281453)
                    ·
                      refine ⟨2215684428570357658980545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5908491809520953757281453 2215684428570357658980545)
                      ·
                        rfl

theorem cell23_4315030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_4315030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315030 prefixEnd_4315030 := by exact prefixLift 4315030
  have htrace : WordTrace (prefixWord ++ tailWord_4315030) baseStart_4315030 baseEnd_4315030 := by
    simpa [prefixWord, tailWord_4315030, baseEnd_4315030] using wordTrace_append hprefix tailTrace_4315030
  have hstable : (prefixWord ++ tailWord_4315030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315030).length < 2 ^ (prefixWord ++ tailWord_4315030).sum := by decide
  have hdescent : baseEnd_4315030 < baseStart_4315030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315065 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 3, 2, 5]
def baseStart_4315065 : Nat := 118140960795 + 4315065 * 2 ^ 59
def prefixEnd_4315065 : Nat := 4983230072969 + 3 ^ 40 * 4315065 * 2
def baseEnd_4315065 : Nat := 2215702400393265022042883

theorem tailTrace_4315065 : CollatzResearch.WordTrace tailWord_4315065 prefixEnd_4315065 2215702400393265022042883 := by
  unfold tailWord_4315065
  simp only [CollatzResearch.WordTrace]
  refine ⟨157383350112263934275170649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104922233408175956183447099 157383350112263934275170649)
  ·
    refine ⟨118037512584197950706377987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157383350112263934275170649 118037512584197950706377987)
    ·
      refine ⟨177056268876296926059566981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118037512584197950706377987 177056268876296926059566981)
      ·
        refine ⟨33198050414305673636168809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177056268876296926059566981 33198050414305673636168809)
        ·
          refine ⟨24898537810729255227126607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33198050414305673636168809 24898537810729255227126607)
          ·
            refine ⟨37347806716093882840689911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24898537810729255227126607 37347806716093882840689911)
            ·
              refine ⟨56021710074140824261034867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37347806716093882840689911 56021710074140824261034867)
              ·
                refine ⟨84032565111211236391552301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56021710074140824261034867 84032565111211236391552301)
                ·
                  refine ⟨31512211916704213646832113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84032565111211236391552301 31512211916704213646832113)
                  ·
                    refine ⟨23634158937528160235124085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 31512211916704213646832113 23634158937528160235124085)
                    ·
                      refine ⟨2215702400393265022042883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23634158937528160235124085 2215702400393265022042883)
                      ·
                        rfl

theorem cell23_4315065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_4315065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315065 prefixEnd_4315065 := by exact prefixLift 4315065
  have htrace : WordTrace (prefixWord ++ tailWord_4315065) baseStart_4315065 baseEnd_4315065 := by
    simpa [prefixWord, tailWord_4315065, baseEnd_4315065] using wordTrace_append hprefix tailTrace_4315065
  have hstable : (prefixWord ++ tailWord_4315065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315065).length < 2 ^ (prefixWord ++ tailWord_4315065).sum := by decide
  have hdescent : baseEnd_4315065 < baseStart_4315065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315092 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_4315092 : Nat := 118140960795 + 4315092 * 2 ^ 59
def prefixEnd_4315092 : Nat := 4983230072969 + 3 ^ 40 * 4315092 * 2
def baseEnd_4315092 : Nat := 2215716264370936416405259

theorem tailTrace_4315092 : CollatzResearch.WordTrace tailWord_4315092 prefixEnd_4315092 2215716264370936416405259 := by
  unfold tailWord_4315092
  simp only [CollatzResearch.WordTrace]
  refine ⟨78692167441583058943201765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104922889922110745257602353 78692167441583058943201765)
  ·
    refine ⟨14754781395296823551850331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78692167441583058943201765 14754781395296823551850331)
    ·
      refine ⟨22132172092945235327775497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14754781395296823551850331 22132172092945235327775497)
      ·
        refine ⟨16599129069708926495831623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22132172092945235327775497 16599129069708926495831623)
        ·
          refine ⟨24898693604563389743747435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16599129069708926495831623 24898693604563389743747435)
          ·
            refine ⟨37348040406845084615621153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24898693604563389743747435 37348040406845084615621153)
            ·
              refine ⟨28011030305133813461715865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37348040406845084615621153 28011030305133813461715865)
              ·
                refine ⟨21008272728850360096286899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28011030305133813461715865 21008272728850360096286899)
                ·
                  refine ⟨31512409093275540144430349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21008272728850360096286899 31512409093275540144430349)
                  ·
                    refine ⟨11817153409978327554161381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31512409093275540144430349 11817153409978327554161381)
                    ·
                      refine ⟨2215716264370936416405259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11817153409978327554161381 2215716264370936416405259)
                      ·
                        rfl

theorem cell23_4315092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_4315092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315092 prefixEnd_4315092 := by exact prefixLift 4315092
  have htrace : WordTrace (prefixWord ++ tailWord_4315092) baseStart_4315092 baseEnd_4315092 := by
    simpa [prefixWord, tailWord_4315092, baseEnd_4315092] using wordTrace_append hprefix tailTrace_4315092
  have hstable : (prefixWord ++ tailWord_4315092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315092).length < 2 ^ (prefixWord ++ tailWord_4315092).sum := by decide
  have hdescent : baseEnd_4315092 < baseStart_4315092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315155 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 7]
def baseStart_4315155 : Nat := 118140960795 + 4315155 * 2 ^ 59
def prefixEnd_4315155 : Nat := 4983230072969 + 3 ^ 40 * 4315155 * 2
def baseEnd_4315155 : Nat := 2215748613652169669917469

theorem tailTrace_4315155 : CollatzResearch.WordTrace tailWord_4315155 prefixEnd_4315155 2215748613652169669917469 := by
  unfold tailWord_4315155
  simp only [CollatzResearch.WordTrace]
  refine ⟨157386632681937879645946919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104924421787958586430631279 157386632681937879645946919)
  ·
    refine ⟨236079949022906819468920379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157386632681937879645946919 236079949022906819468920379)
    ·
      refine ⟨354119923534360229203380569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236079949022906819468920379 354119923534360229203380569)
      ·
        refine ⟨265589942650770171902535427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354119923534360229203380569 265589942650770171902535427)
        ·
          refine ⟨398384913976155257853803141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265589942650770171902535427 398384913976155257853803141)
          ·
            refine ⟨74697171370529110847588089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 398384913976155257853803141 74697171370529110847588089)
            ·
              refine ⟨56022878527896833135691067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74697171370529110847588089 56022878527896833135691067)
              ·
                refine ⟨84034317791845249703536601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56022878527896833135691067 84034317791845249703536601)
                ·
                  refine ⟨63025738343883937277652451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84034317791845249703536601 63025738343883937277652451)
                  ·
                    refine ⟨94538607515825905916478677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63025738343883937277652451 94538607515825905916478677)
                    ·
                      refine ⟨2215748613652169669917469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94538607515825905916478677 2215748613652169669917469)
                      ·
                        rfl

theorem cell23_4315155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_4315155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315155 prefixEnd_4315155 := by exact prefixLift 4315155
  have htrace : WordTrace (prefixWord ++ tailWord_4315155) baseStart_4315155 baseEnd_4315155 := by
    simpa [prefixWord, tailWord_4315155, baseEnd_4315155] using wordTrace_append hprefix tailTrace_4315155
  have hstable : (prefixWord ++ tailWord_4315155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315155).length < 2 ^ (prefixWord ++ tailWord_4315155).sum := by decide
  have hdescent : baseEnd_4315155 < baseStart_4315155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315186 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2]
def baseStart_4315186 : Nat := 118140960795 + 4315186 * 2 ^ 59
def prefixEnd_4315186 : Nat := 4983230072969 + 3 ^ 40 * 4315186 * 2
def baseEnd_4315186 : Nat := 2215764531552459048629827

theorem tailTrace_4315186 : CollatzResearch.WordTrace tailWord_4315186 prefixEnd_4315186 2215764531552459048629827 := by
  unfold tailWord_4315186
  simp only [CollatzResearch.WordTrace]
  refine ⟨39346940836206392985081353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104925175563217047960216941 39346940836206392985081353)
  ·
    refine ⟨29510205627154794738811015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39346940836206392985081353 29510205627154794738811015)
    ·
      refine ⟨44265308440732192108216523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29510205627154794738811015 44265308440732192108216523)
      ·
        refine ⟨66397962661098288162324785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44265308440732192108216523 66397962661098288162324785)
        ·
          refine ⟨49798471995823716121743589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66397962661098288162324785 49798471995823716121743589)
          ·
            refine ⟨9337213499216946772826923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49798471995823716121743589 9337213499216946772826923)
            ·
              refine ⟨14005820248825420159240385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9337213499216946772826923 14005820248825420159240385)
              ·
                refine ⟨10504365186619065119430289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14005820248825420159240385 10504365186619065119430289)
                ·
                  refine ⟨7878273889964298839572717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10504365186619065119430289 7878273889964298839572717)
                  ·
                    refine ⟨2954352708736612064839769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7878273889964298839572717 2954352708736612064839769)
                    ·
                      refine ⟨2215764531552459048629827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2954352708736612064839769 2215764531552459048629827)
                      ·
                        rfl

theorem cell23_4315186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_4315186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315186 prefixEnd_4315186 := by exact prefixLift 4315186
  have htrace : WordTrace (prefixWord ++ tailWord_4315186) baseStart_4315186 baseEnd_4315186 := by
    simpa [prefixWord, tailWord_4315186, baseEnd_4315186] using wordTrace_append hprefix tailTrace_4315186
  have hstable : (prefixWord ++ tailWord_4315186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315186).length < 2 ^ (prefixWord ++ tailWord_4315186).sum := by decide
  have hdescent : baseEnd_4315186 < baseStart_4315186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315193 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 3, 1, 3]
def baseStart_4315193 : Nat := 118140960795 + 4315193 * 2 ^ 59
def prefixEnd_4315193 : Nat := 4983230072969 + 3 ^ 40 * 4315193 * 2
def baseEnd_4315193 : Nat := 2215768125917040521242295

theorem tailTrace_4315193 : CollatzResearch.WordTrace tailWord_4315193 prefixEnd_4315193 2215768125917040521242295 := by
  unfold tailWord_4315193
  simp only [CollatzResearch.WordTrace]
  refine ⟨157388018655800212135830233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104925345770533474757220155 157388018655800212135830233)
  ·
    refine ⟨118041013991850159101872675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157388018655800212135830233 118041013991850159101872675)
    ·
      refine ⟨177061520987775238652809013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118041013991850159101872675 177061520987775238652809013)
      ·
        refine ⟨16599517592603928623700845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 177061520987775238652809013 16599517592603928623700845)
        ·
          refine ⟨6224819097226473233887817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16599517592603928623700845 6224819097226473233887817)
          ·
            refine ⟨4668614322919854925415863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6224819097226473233887817 4668614322919854925415863)
            ·
              refine ⟨7002921484379782388123795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4668614322919854925415863 7002921484379782388123795)
              ·
                refine ⟨10504382226569673582185693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7002921484379782388123795 10504382226569673582185693)
                ·
                  refine ⟨3939143334963627593319635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10504382226569673582185693 3939143334963627593319635)
                  ·
                    refine ⟨5908715002445441389979453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3939143334963627593319635 5908715002445441389979453)
                    ·
                      refine ⟨2215768125917040521242295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5908715002445441389979453 2215768125917040521242295)
                      ·
                        rfl

theorem cell23_4315193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_4315193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315193 prefixEnd_4315193 := by exact prefixLift 4315193
  have htrace : WordTrace (prefixWord ++ tailWord_4315193) baseStart_4315193 baseEnd_4315193 := by
    simpa [prefixWord, tailWord_4315193, baseEnd_4315193] using wordTrace_append hprefix tailTrace_4315193
  have hstable : (prefixWord ++ tailWord_4315193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315193).length < 2 ^ (prefixWord ++ tailWord_4315193).sum := by decide
  have hdescent : baseEnd_4315193 < baseStart_4315193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315209 : List Nat := [1, 2, 1, 1, 2, 2, 5, 3, 2, 4]
def baseStart_4315209 : Nat := 118140960795 + 4315209 * 2 ^ 59
def prefixEnd_4315209 : Nat := 4983230072969 + 3 ^ 40 * 4315209 * 2
def baseEnd_4315209 : Nat := 738592113869170819547407

theorem tailTrace_4315209 : CollatzResearch.WordTrace tailWord_4315209 prefixEnd_4315209 738592113869170819547407 := by
  unfold tailWord_4315209
  simp only [CollatzResearch.WordTrace]
  refine ⟨157388602223742246868412681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104925734815828164578941787 157388602223742246868412681)
  ·
    refine ⟨118041451667806685151309511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157388602223742246868412681 118041451667806685151309511)
    ·
      refine ⟨177062177501710027726964267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118041451667806685151309511 177062177501710027726964267)
      ·
        refine ⟨265593266252565041590446401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177062177501710027726964267 265593266252565041590446401)
        ·
          refine ⟨199194949689423781192834801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265593266252565041590446401 199194949689423781192834801)
          ·
            refine ⟨149396212267067835894626101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199194949689423781192834801 149396212267067835894626101)
            ·
              refine ⟨14005894900037609615121197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 149396212267067835894626101 14005894900037609615121197)
              ·
                refine ⟨5252210587514103605670449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14005894900037609615121197 5252210587514103605670449)
                ·
                  refine ⟨3939157940635577704252837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5252210587514103605670449 3939157940635577704252837)
                  ·
                    refine ⟨738592113869170819547407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3939157940635577704252837 738592113869170819547407)
                    ·
                      rfl

theorem cell23_4315209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 2, 4].length) (baseStart_4315209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315209 prefixEnd_4315209 := by exact prefixLift 4315209
  have htrace : WordTrace (prefixWord ++ tailWord_4315209) baseStart_4315209 baseEnd_4315209 := by
    simpa [prefixWord, tailWord_4315209, baseEnd_4315209] using wordTrace_append hprefix tailTrace_4315209
  have hstable : (prefixWord ++ tailWord_4315209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315209).length < 2 ^ (prefixWord ++ tailWord_4315209).sum := by decide
  have hdescent : baseEnd_4315209 < baseStart_4315209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315212 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 1, 1, 6]
def baseStart_4315212 : Nat := 118140960795 + 4315212 * 2 ^ 59
def prefixEnd_4315212 : Nat := 4983230072969 + 3 ^ 40 * 4315212 * 2
def baseEnd_4315212 : Nat := 2215777882049475946904707

theorem tailTrace_4315212 : CollatzResearch.WordTrace tailWord_4315212 prefixEnd_4315212 2215777882049475946904707 := by
  unfold tailWord_4315212
  simp only [CollatzResearch.WordTrace]
  refine ⟨78694355821365689190385945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104925807761820918920514593 78694355821365689190385945)
  ·
    refine ⟨59020766866024266892789459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78694355821365689190385945 59020766866024266892789459)
    ·
      refine ⟨88531150299036400339184189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59020766866024266892789459 88531150299036400339184189)
      ·
        refine ⟨33199181362138650127194071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88531150299036400339184189 33199181362138650127194071)
        ·
          refine ⟨49798772043207975190791107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33199181362138650127194071 49798772043207975190791107)
          ·
            refine ⟨74698158064811962786186661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49798772043207975190791107 74698158064811962786186661)
            ·
              refine ⟨14005904637152243022409999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74698158064811962786186661 14005904637152243022409999)
              ·
                refine ⟨21008856955728364533614999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14005904637152243022409999 21008856955728364533614999)
                ·
                  refine ⟨31513285433592546800422499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21008856955728364533614999 31513285433592546800422499)
                  ·
                    refine ⟨47269928150388820200633749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31513285433592546800422499 47269928150388820200633749)
                    ·
                      refine ⟨2215777882049475946904707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47269928150388820200633749 2215777882049475946904707)
                      ·
                        rfl

theorem cell23_4315212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_4315212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315212 prefixEnd_4315212 := by exact prefixLift 4315212
  have htrace : WordTrace (prefixWord ++ tailWord_4315212) baseStart_4315212 baseEnd_4315212 := by
    simpa [prefixWord, tailWord_4315212, baseEnd_4315212] using wordTrace_append hprefix tailTrace_4315212
  have hstable : (prefixWord ++ tailWord_4315212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315212).length < 2 ^ (prefixWord ++ tailWord_4315212).sum := by decide
  have hdescent : baseEnd_4315212 < baseStart_4315212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315233 : List Nat := [1, 2, 3, 1, 1, 2, 1, 7, 1, 2, 2]
def baseStart_4315233 : Nat := 118140960795 + 4315233 * 2 ^ 59
def prefixEnd_4315233 : Nat := 4983230072969 + 3 ^ 40 * 4315233 * 2
def baseEnd_4315233 : Nat := 2215788665143220364742111

theorem tailTrace_4315233 : CollatzResearch.WordTrace tailWord_4315233 prefixEnd_4315233 2215788665143220364742111 := by
  unfold tailWord_4315233
  simp only [CollatzResearch.WordTrace]
  refine ⟨157389477575655298967286353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104926318383770199311524235 157389477575655298967286353)
  ·
    refine ⟨118042108181741474225464765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157389477575655298967286353 118042108181741474225464765)
    ·
      refine ⟨44265790568153052834549287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118042108181741474225464765 44265790568153052834549287)
      ·
        refine ⟨66398685852229579251823931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44265790568153052834549287 66398685852229579251823931)
        ·
          refine ⟨99598028778344368877735897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66398685852229579251823931 99598028778344368877735897)
          ·
            refine ⟨74698521583758276658301923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99598028778344368877735897 74698521583758276658301923)
            ·
              refine ⟨112047782375637414987452885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74698521583758276658301923 112047782375637414987452885)
              ·
                refine ⟨2626119899429001913768427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 112047782375637414987452885 2626119899429001913768427)
                ·
                  refine ⟨3939179849143502870652641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2626119899429001913768427 3939179849143502870652641)
                  ·
                    refine ⟨2954384886857627152989481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3939179849143502870652641 2954384886857627152989481)
                    ·
                      refine ⟨2215788665143220364742111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2954384886857627152989481 2215788665143220364742111)
                      ·
                        rfl

theorem cell23_4315233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_4315233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315233 prefixEnd_4315233 := by exact prefixLift 4315233
  have htrace : WordTrace (prefixWord ++ tailWord_4315233) baseStart_4315233 baseEnd_4315233 := by
    simpa [prefixWord, tailWord_4315233, baseEnd_4315233] using wordTrace_append hprefix tailTrace_4315233
  have hstable : (prefixWord ++ tailWord_4315233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315233).length < 2 ^ (prefixWord ++ tailWord_4315233).sum := by decide
  have hdescent : baseEnd_4315233 < baseStart_4315233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315250 : List Nat := [3, 2, 1, 2, 2, 3, 1, 4, 1, 2, 2]
def baseStart_4315250 : Nat := 118140960795 + 4315250 * 2 ^ 59
def prefixEnd_4315250 : Nat := 4983230072969 + 3 ^ 40 * 4315250 * 2
def baseEnd_4315250 : Nat := 2215797394314346798229533

theorem tailTrace_4315250 : CollatzResearch.WordTrace tailWord_4315250 prefixEnd_4315250 2215797394314346798229533 := by
  unfold tailWord_4315250
  simp only [CollatzResearch.WordTrace]
  refine ⟨39347524404148427717663801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104926731744395807247103469 39347524404148427717663801)
  ·
    refine ⟨29510643303111320788247851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39347524404148427717663801 29510643303111320788247851)
    ·
      refine ⟨44265964954666981182371777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29510643303111320788247851 44265964954666981182371777)
      ·
        refine ⟨33199473716000235886778833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44265964954666981182371777 33199473716000235886778833)
        ·
          refine ⟨24899605287000176915084125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33199473716000235886778833 24899605287000176915084125)
          ·
            refine ⟨9337351982625066343156547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24899605287000176915084125 9337351982625066343156547)
            ·
              refine ⟨14006027973937599514734821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9337351982625066343156547 14006027973937599514734821)
              ·
                refine ⟨2626130245113299909012779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14006027973937599514734821 2626130245113299909012779)
                ·
                  refine ⟨3939195367669949863519169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2626130245113299909012779 3939195367669949863519169)
                  ·
                    refine ⟨2954396525752462397639377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3939195367669949863519169 2954396525752462397639377)
                    ·
                      refine ⟨2215797394314346798229533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2954396525752462397639377 2215797394314346798229533)
                      ·
                        rfl

theorem cell23_4315250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_4315250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315250 prefixEnd_4315250 := by exact prefixLift 4315250
  have htrace : WordTrace (prefixWord ++ tailWord_4315250) baseStart_4315250 baseEnd_4315250 := by
    simpa [prefixWord, tailWord_4315250, baseEnd_4315250] using wordTrace_append hprefix tailTrace_4315250
  have hstable : (prefixWord ++ tailWord_4315250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315250).length < 2 ^ (prefixWord ++ tailWord_4315250).sum := by decide
  have hdescent : baseEnd_4315250 < baseStart_4315250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315284 : List Nat := [2, 4, 2, 3, 1, 1, 2, 3, 1, 2, 2]
def baseStart_4315284 : Nat := 118140960795 + 4315284 * 2 ^ 59
def prefixEnd_4315284 : Nat := 4983230072969 + 3 ^ 40 * 4315284 * 2
def baseEnd_4315284 : Nat := 2215814852656599665204377

theorem tailTrace_4315284 : CollatzResearch.WordTrace tailWord_4315284 prefixEnd_4315284 2215814852656599665204377 := by
  unfold tailWord_4315284
  simp only [CollatzResearch.WordTrace]
  refine ⟨78695668849235267338696453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104927558465647023118261937 78695668849235267338696453)
  ·
    refine ⟨14755437909231612626005585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78695668849235267338696453 14755437909231612626005585)
    ·
      refine ⟨11066578431923709469504189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14755437909231612626005585 11066578431923709469504189)
      ·
        refine ⟨4149966911971391051064071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11066578431923709469504189 4149966911971391051064071)
        ·
          refine ⟨6224950367957086576596107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4149966911971391051064071 6224950367957086576596107)
          ·
            refine ⟨9337425551935629864894161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6224950367957086576596107 9337425551935629864894161)
            ·
              refine ⟨7003069163951722398670621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9337425551935629864894161 7003069163951722398670621)
              ·
                refine ⟨2626150936481895899501483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7003069163951722398670621 2626150936481895899501483)
                ·
                  refine ⟨3939226404722843849252225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2626150936481895899501483 3939226404722843849252225)
                  ·
                    refine ⟨2954419803542132886939169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3939226404722843849252225 2954419803542132886939169)
                    ·
                      refine ⟨2215814852656599665204377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2954419803542132886939169 2215814852656599665204377)
                      ·
                        rfl

theorem cell23_4315284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_4315284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315284 prefixEnd_4315284 := by exact prefixLift 4315284
  have htrace : WordTrace (prefixWord ++ tailWord_4315284) baseStart_4315284 baseEnd_4315284 := by
    simpa [prefixWord, tailWord_4315284, baseEnd_4315284] using wordTrace_append hprefix tailTrace_4315284
  have hstable : (prefixWord ++ tailWord_4315284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315284).length < 2 ^ (prefixWord ++ tailWord_4315284).sum := by decide
  have hdescent : baseEnd_4315284 < baseStart_4315284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315293 : List Nat := [1, 4, 2, 1, 1, 4, 1, 3, 1, 3, 2]
def baseStart_4315293 : Nat := 118140960795 + 4315293 * 2 ^ 59
def prefixEnd_4315293 : Nat := 4983230072969 + 3 ^ 40 * 4315293 * 2
def baseEnd_4315293 : Nat := 2215819473982490129991835

theorem tailTrace_4315293 : CollatzResearch.WordTrace tailWord_4315293 prefixEnd_4315293 2215819473982490129991835 := by
  unfold tailWord_4315293
  simp only [CollatzResearch.WordTrace]
  refine ⟨157391665955437929214470533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104927777303625286142980355 157391665955437929214470533)
  ·
    refine ⟨29510937366644611727713225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157391665955437929214470533 29510937366644611727713225)
    ·
      refine ⟨22133203024983458795784919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29510937366644611727713225 22133203024983458795784919)
      ·
        refine ⟨33199804537475188193677379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22133203024983458795784919 33199804537475188193677379)
        ·
          refine ⟨49799706806212782290516069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33199804537475188193677379 49799706806212782290516069)
          ·
            refine ⟨9337445026164896679471763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 49799706806212782290516069 9337445026164896679471763)
            ·
              refine ⟨14006167539247345019207645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9337445026164896679471763 14006167539247345019207645)
              ·
                refine ⟨5252312827217754382202867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14006167539247345019207645 5252312827217754382202867)
                ·
                  refine ⟨7878469240826631573304301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5252312827217754382202867 7878469240826631573304301)
                  ·
                    refine ⟨2954425965309986839989113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7878469240826631573304301 2954425965309986839989113)
                    ·
                      refine ⟨2215819473982490129991835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2954425965309986839989113 2215819473982490129991835)
                      ·
                        rfl

theorem cell23_4315293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_4315293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315293 prefixEnd_4315293 := by exact prefixLift 4315293
  have htrace : WordTrace (prefixWord ++ tailWord_4315293) baseStart_4315293 baseEnd_4315293 := by
    simpa [prefixWord, tailWord_4315293, baseEnd_4315293] using wordTrace_append hprefix tailTrace_4315293
  have hstable : (prefixWord ++ tailWord_4315293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315293).length < 2 ^ (prefixWord ++ tailWord_4315293).sum := by decide
  have hdescent : baseEnd_4315293 < baseStart_4315293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315300 : List Nat := [2, 3, 1, 2, 4, 2, 1, 2, 2, 1, 3]
def baseStart_4315300 : Nat := 118140960795 + 4315300 * 2 ^ 59
def prefixEnd_4315300 : Nat := 4983230072969 + 3 ^ 40 * 4315300 * 2
def baseEnd_4315300 : Nat := 2215823068347071602604303

theorem tailTrace_4315300 : CollatzResearch.WordTrace tailWord_4315300 prefixEnd_4315300 2215823068347071602604303 := by
  unfold tailWord_4315300
  simp only [CollatzResearch.WordTrace]
  refine ⟨78695960633206284704987677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104927947510941712939983569 78695960633206284704987677)
  ·
    refine ⟨29510985237452356764370379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78695960633206284704987677 29510985237452356764370379)
    ·
      refine ⟨44266477856178535146555569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29510985237452356764370379 44266477856178535146555569)
      ·
        refine ⟨33199858392133901359916677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44266477856178535146555569 33199858392133901359916677)
        ·
          refine ⟨6224973448525106504984377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33199858392133901359916677 6224973448525106504984377)
          ·
            refine ⟨4668730086393829878738283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6224973448525106504984377 4668730086393829878738283)
            ·
              refine ⟨7003095129590744818107425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4668730086393829878738283 7003095129590744818107425)
              ·
                refine ⟨5252321347193058613580569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7003095129590744818107425 5252321347193058613580569)
                ·
                  refine ⟨3939241010394793960185427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5252321347193058613580569 3939241010394793960185427)
                  ·
                    refine ⟨5908861515592190940278141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3939241010394793960185427 5908861515592190940278141)
                    ·
                      refine ⟨2215823068347071602604303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5908861515592190940278141 2215823068347071602604303)
                      ·
                        rfl

theorem cell23_4315300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_4315300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315300 prefixEnd_4315300 := by exact prefixLift 4315300
  have htrace : WordTrace (prefixWord ++ tailWord_4315300) baseStart_4315300 baseEnd_4315300 := by
    simpa [prefixWord, tailWord_4315300, baseEnd_4315300] using wordTrace_append hprefix tailTrace_4315300
  have hstable : (prefixWord ++ tailWord_4315300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315300).length < 2 ^ (prefixWord ++ tailWord_4315300).sum := by decide
  have hdescent : baseEnd_4315300 < baseStart_4315300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315317 : List Nat := [1, 3, 3, 4, 1, 1, 3, 1, 2, 1, 3]
def baseStart_4315317 : Nat := 118140960795 + 4315317 * 2 ^ 59
def prefixEnd_4315317 : Nat := 4983230072969 + 3 ^ 40 * 4315317 * 2
def baseEnd_4315317 : Nat := 2215831797518198036091725

theorem tailTrace_4315317 : CollatzResearch.WordTrace tailWord_4315317 prefixEnd_4315317 2215831797518198036091725 := by
  unfold tailWord_4315317
  simp only [CollatzResearch.WordTrace]
  refine ⟨157392541307350981313344205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104928360871567320875562803 157392541307350981313344205)
  ·
    refine ⟨59022202990256617992504077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157392541307350981313344205 59022202990256617992504077)
    ·
      refine ⟨22133326121346231747189029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59022202990256617992504077 22133326121346231747189029)
      ·
        refine ⟨4149998647752418452597943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22133326121346231747189029 4149998647752418452597943)
        ·
          refine ⟨6224997971628627678896915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4149998647752418452597943 6224997971628627678896915)
          ·
            refine ⟨9337496957442941518345373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6224997971628627678896915 9337496957442941518345373)
            ·
              refine ⟨3501561359041103069379515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9337496957442941518345373 3501561359041103069379515)
              ·
                refine ⟨5252342038561654604069273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3501561359041103069379515 5252342038561654604069273)
                ·
                  refine ⟨3939256528921240953051955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5252342038561654604069273 3939256528921240953051955)
                  ·
                    refine ⟨5908884793381861429577933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3939256528921240953051955 5908884793381861429577933)
                    ·
                      refine ⟨2215831797518198036091725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5908884793381861429577933 2215831797518198036091725)
                      ·
                        rfl

theorem cell23_4315317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_4315317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315317 prefixEnd_4315317 := by exact prefixLift 4315317
  have htrace : WordTrace (prefixWord ++ tailWord_4315317) baseStart_4315317 baseEnd_4315317 := by
    simpa [prefixWord, tailWord_4315317, baseEnd_4315317] using wordTrace_append hprefix tailTrace_4315317
  have hstable : (prefixWord ++ tailWord_4315317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315317).length < 2 ^ (prefixWord ++ tailWord_4315317).sum := by decide
  have hdescent : baseEnd_4315317 < baseStart_4315317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315319 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 4]
def baseStart_4315319 : Nat := 118140960795 + 4315319 * 2 ^ 59
def prefixEnd_4315319 : Nat := 4983230072969 + 3 ^ 40 * 4315319 * 2
def baseEnd_4315319 : Nat := 2215832824479507028266715

theorem tailTrace_4315319 : CollatzResearch.WordTrace tailWord_4315319 prefixEnd_4315319 2215832824479507028266715 := by
  unfold tailWord_4315319
  simp only [CollatzResearch.WordTrace]
  refine ⟨157392614253343735654917011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104928409502229157103278007 157392614253343735654917011)
  ·
    refine ⟨236088921380015603482375517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157392614253343735654917011 236088921380015603482375517)
    ·
      refine ⟨88533345517505851305890819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236088921380015603482375517 88533345517505851305890819)
      ·
        refine ⟨132800018276258776958836229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88533345517505851305890819 132800018276258776958836229)
        ·
          refine ⟨24900003426798520679781793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132800018276258776958836229 24900003426798520679781793)
          ·
            refine ⟨18675002570098890509836345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24900003426798520679781793 18675002570098890509836345)
            ·
              refine ⟨14006251927574167882377259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18675002570098890509836345 14006251927574167882377259)
              ·
                refine ⟨21009377891361251823565889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14006251927574167882377259 21009377891361251823565889)
                ·
                  refine ⟨15757033418520938867674417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21009377891361251823565889 15757033418520938867674417)
                  ·
                    refine ⟨11817775063890704150755813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15757033418520938867674417 11817775063890704150755813)
                    ·
                      refine ⟨2215832824479507028266715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11817775063890704150755813 2215832824479507028266715)
                      ·
                        rfl

theorem cell23_4315319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 4].length) (baseStart_4315319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315319 prefixEnd_4315319 := by exact prefixLift 4315319
  have htrace : WordTrace (prefixWord ++ tailWord_4315319) baseStart_4315319 baseEnd_4315319 := by
    simpa [prefixWord, tailWord_4315319, baseEnd_4315319] using wordTrace_append hprefix tailTrace_4315319
  have hstable : (prefixWord ++ tailWord_4315319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315319).length < 2 ^ (prefixWord ++ tailWord_4315319).sum := by decide
  have hdescent : baseEnd_4315319 < baseStart_4315319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315363 : List Nat := [1, 1, 1, 8, 1, 2, 1, 1, 7]
def baseStart_4315363 : Nat := 118140960795 + 4315363 * 2 ^ 59
def prefixEnd_4315363 : Nat := 4983230072969 + 3 ^ 40 * 4315363 * 2
def baseEnd_4315363 : Nat := 246206157514256095124057

theorem tailTrace_4315363 : CollatzResearch.WordTrace tailWord_4315363 prefixEnd_4315363 246206157514256095124057 := by
  unfold tailWord_4315363
  simp only [CollatzResearch.WordTrace]
  refine ⟨157394219065184331169518743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104929479376789554113012495 157394219065184331169518743)
  ·
    refine ⟨236091328597776496754278115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157394219065184331169518743 236091328597776496754278115)
    ·
      refine ⟨354136992896664745131417173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236091328597776496754278115 354136992896664745131417173)
      ·
        refine ⟨4150042885507789982008795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 354136992896664745131417173 4150042885507789982008795)
        ·
          refine ⟨6225064328261684973013193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4150042885507789982008795 6225064328261684973013193)
          ·
            refine ⟨4668798246196263729759895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6225064328261684973013193 4668798246196263729759895)
            ·
              refine ⟨7003197369294395594639843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4668798246196263729759895 7003197369294395594639843)
              ·
                refine ⟨10504796053941593391959765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7003197369294395594639843 10504796053941593391959765)
                ·
                  refine ⟨246206157514256095124057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10504796053941593391959765 246206157514256095124057)
                  ·
                    rfl

theorem cell23_4315363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 1, 7].length) (baseStart_4315363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315363 prefixEnd_4315363 := by exact prefixLift 4315363
  have htrace : WordTrace (prefixWord ++ tailWord_4315363) baseStart_4315363 baseEnd_4315363 := by
    simpa [prefixWord, tailWord_4315363, baseEnd_4315363] using wordTrace_append hprefix tailTrace_4315363
  have hstable : (prefixWord ++ tailWord_4315363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315363).length < 2 ^ (prefixWord ++ tailWord_4315363).sum := by decide
  have hdescent : baseEnd_4315363 < baseStart_4315363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315379 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 4]
def baseStart_4315379 : Nat := 118140960795 + 4315379 * 2 ^ 59
def prefixEnd_4315379 : Nat := 4983230072969 + 3 ^ 40 * 4315379 * 2
def baseEnd_4315379 : Nat := 2215863633318776793516439

theorem tailTrace_4315379 : CollatzResearch.WordTrace tailWord_4315379 prefixEnd_4315379 2215863633318776793516439 := by
  unfold tailWord_4315379
  simp only [CollatzResearch.WordTrace]
  refine ⟨157394802633126365902101191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104929868422084243934734127 157394802633126365902101191)
  ·
    refine ⟨236092203949689548853151787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157394802633126365902101191 236092203949689548853151787)
    ·
      refine ⟨354138305924534323279727681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236092203949689548853151787 354138305924534323279727681)
      ·
        refine ⟨265603729443400742459795761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354138305924534323279727681 265603729443400742459795761)
        ·
          refine ⟨199202797082550556844846821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265603729443400742459795761 199202797082550556844846821)
          ·
            refine ⟨37350524452978229408408779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 199202797082550556844846821 37350524452978229408408779)
            ·
              refine ⟨56025786679467344112613169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37350524452978229408408779 56025786679467344112613169)
              ·
                refine ⟨42019340009600508084459877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56025786679467344112613169 42019340009600508084459877)
                ·
                  refine ⟨7878626251800095265836227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42019340009600508084459877 7878626251800095265836227)
                  ·
                    refine ⟨11817939377700142898754341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7878626251800095265836227 11817939377700142898754341)
                    ·
                      refine ⟨2215863633318776793516439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11817939377700142898754341 2215863633318776793516439)
                      ·
                        rfl

theorem cell23_4315379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 4].length) (baseStart_4315379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315379 prefixEnd_4315379 := by exact prefixLift 4315379
  have htrace : WordTrace (prefixWord ++ tailWord_4315379) baseStart_4315379 baseEnd_4315379 := by
    simpa [prefixWord, tailWord_4315379, baseEnd_4315379] using wordTrace_append hprefix tailTrace_4315379
  have hstable : (prefixWord ++ tailWord_4315379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315379).length < 2 ^ (prefixWord ++ tailWord_4315379).sum := by decide
  have hdescent : baseEnd_4315379 < baseStart_4315379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315416 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 2, 2, 3]
def baseStart_4315416 : Nat := 118140960795 + 4315416 * 2 ^ 59
def prefixEnd_4315416 : Nat := 4983230072969 + 3 ^ 40 * 4315416 * 2
def baseEnd_4315416 : Nat := 2215882632102993148753769

theorem tailTrace_4315416 : CollatzResearch.WordTrace tailWord_4315416 prefixEnd_4315416 2215882632102993148753769 := by
  unfold tailWord_4315416
  simp only [CollatzResearch.WordTrace]
  refine ⟨78698076066996160610599051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104930768089328214147465401 78698076066996160610599051)
  ·
    refine ⟨118047114100494240915898577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78698076066996160610599051 118047114100494240915898577)
    ·
      refine ⟨88535335575370680686923933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118047114100494240915898577 88535335575370680686923933)
      ·
        refine ⟨33200750840764005257596475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88535335575370680686923933 33200750840764005257596475)
        ·
          refine ⟨49801126261146007886394713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33200750840764005257596475 49801126261146007886394713)
          ·
            refine ⟨37350844695859505914796035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49801126261146007886394713 37350844695859505914796035)
            ·
              refine ⟨56026267043789258872194053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37350844695859505914796035 56026267043789258872194053)
              ·
                refine ⟨10504925070710486038536385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56026267043789258872194053 10504925070710486038536385)
                ·
                  refine ⟨7878693803032864528902289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10504925070710486038536385 7878693803032864528902289)
                  ·
                    refine ⟨5909020352274648396676717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7878693803032864528902289 5909020352274648396676717)
                    ·
                      refine ⟨2215882632102993148753769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5909020352274648396676717 2215882632102993148753769)
                      ·
                        rfl

theorem cell23_4315416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_4315416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315416 prefixEnd_4315416 := by exact prefixLift 4315416
  have htrace : WordTrace (prefixWord ++ tailWord_4315416) baseStart_4315416 baseEnd_4315416 := by
    simpa [prefixWord, tailWord_4315416, baseEnd_4315416] using wordTrace_append hprefix tailTrace_4315416
  have hstable : (prefixWord ++ tailWord_4315416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315416).length < 2 ^ (prefixWord ++ tailWord_4315416).sum := by decide
  have hdescent : baseEnd_4315416 < baseStart_4315416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315419 : List Nat := [1, 1, 1, 1, 1, 1, 7, 4, 6]
def baseStart_4315419 : Nat := 118140960795 + 4315419 * 2 ^ 59
def prefixEnd_4315419 : Nat := 4983230072969 + 3 ^ 40 * 4315419 * 2
def baseEnd_4315419 : Nat := 246209352504995181890695

theorem tailTrace_4315419 : CollatzResearch.WordTrace tailWord_4315419 prefixEnd_4315419 246209352504995181890695 := by
  unfold tailWord_4315419
  simp only [CollatzResearch.WordTrace]
  refine ⟨157396261552981452733557311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104930841035320968489038207 157396261552981452733557311)
  ·
    refine ⟨236094392329472179100335967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157396261552981452733557311 236094392329472179100335967)
    ·
      refine ⟨354141588494208268650503951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236094392329472179100335967 354141588494208268650503951)
      ·
        refine ⟨531212382741312402975755927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354141588494208268650503951 531212382741312402975755927)
        ·
          refine ⟨796818574111968604463633891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531212382741312402975755927 796818574111968604463633891)
          ·
            refine ⟨1195227861167952906695450837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796818574111968604463633891 1195227861167952906695450837)
            ·
              refine ⟨28013152996123896250674629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1195227861167952906695450837 28013152996123896250674629)
              ·
                refine ⟨5252466186773230547001493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28013152996123896250674629 5252466186773230547001493)
                ·
                  refine ⟨246209352504995181890695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5252466186773230547001493 246209352504995181890695)
                  ·
                    rfl

theorem cell23_4315419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 4, 6].length) (baseStart_4315419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315419 prefixEnd_4315419 := by exact prefixLift 4315419
  have htrace : WordTrace (prefixWord ++ tailWord_4315419) baseStart_4315419 baseEnd_4315419 := by
    simpa [prefixWord, tailWord_4315419, baseEnd_4315419] using wordTrace_append hprefix tailTrace_4315419
  have hstable : (prefixWord ++ tailWord_4315419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315419).length < 2 ^ (prefixWord ++ tailWord_4315419).sum := by decide
  have hdescent : baseEnd_4315419 < baseStart_4315419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315457 : List Nat := [1, 2, 5, 2, 2, 1, 2, 3, 1, 4]
def baseStart_4315457 : Nat := 118140960795 + 4315457 * 2 ^ 59
def prefixEnd_4315457 : Nat := 4983230072969 + 3 ^ 40 * 4315457 * 2
def baseEnd_4315457 : Nat := 738634561603275829447027

theorem tailTrace_4315457 : CollatzResearch.WordTrace tailWord_4315457 prefixEnd_4315457 738634561603275829447027 := by
  unfold tailWord_4315457
  simp only [CollatzResearch.WordTrace]
  refine ⟨157397647526843785223440625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104931765017895856815627083 157397647526843785223440625)
  ·
    refine ⟨118048235645132838917580469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157397647526843785223440625 118048235645132838917580469)
    ·
      refine ⟨11067022091731203648523169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 118048235645132838917580469 11067022091731203648523169)
      ·
        refine ⟨8300266568798402736392377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11067022091731203648523169 8300266568798402736392377)
        ·
          refine ⟨6225199926598802052294283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8300266568798402736392377 6225199926598802052294283)
          ·
            refine ⟨9337799889898203078441425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6225199926598802052294283 9337799889898203078441425)
            ·
              refine ⟨7003349917423652308831069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9337799889898203078441425 7003349917423652308831069)
              ·
                refine ⟨2626256219033869615811651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7003349917423652308831069 2626256219033869615811651)
                ·
                  refine ⟨3939384328550804423717477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2626256219033869615811651 3939384328550804423717477)
                  ·
                    refine ⟨738634561603275829447027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3939384328550804423717477 738634561603275829447027)
                    ·
                      rfl

theorem cell23_4315457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_4315457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315457 prefixEnd_4315457 := by exact prefixLift 4315457
  have htrace : WordTrace (prefixWord ++ tailWord_4315457) baseStart_4315457 baseEnd_4315457 := by
    simpa [prefixWord, tailWord_4315457, baseEnd_4315457] using wordTrace_append hprefix tailTrace_4315457
  have hstable : (prefixWord ++ tailWord_4315457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315457).length < 2 ^ (prefixWord ++ tailWord_4315457).sum := by decide
  have hdescent : baseEnd_4315457 < baseStart_4315457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315499 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 6]
def baseStart_4315499 : Nat := 118140960795 + 4315499 * 2 ^ 59
def prefixEnd_4315499 : Nat := 4983230072969 + 3 ^ 40 * 4315499 * 2
def baseEnd_4315499 : Nat := 2215925250997316324015887

theorem tailTrace_4315499 : CollatzResearch.WordTrace tailWord_4315499 prefixEnd_4315499 2215925250997316324015887 := by
  unfold tailWord_4315499
  simp only [CollatzResearch.WordTrace]
  refine ⟨157399179392691626396469551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104932786261794417597646367 157399179392691626396469551)
  ·
    refine ⟨236098769089037439594704327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157399179392691626396469551 236098769089037439594704327)
    ·
      refine ⟨354148153633556159392056491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236098769089037439594704327 354148153633556159392056491)
      ·
        refine ⟨531222230450334239088084737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354148153633556159392056491 531222230450334239088084737)
        ·
          refine ⟨398416672837750679316063553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 531222230450334239088084737 398416672837750679316063553)
          ·
            refine ⟨298812504628313009487047665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398416672837750679316063553 298812504628313009487047665)
            ·
              refine ⟨224109378471234757115285749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298812504628313009487047665 224109378471234757115285749)
              ·
                refine ⟨21010254231678258479558039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 224109378471234757115285749 21010254231678258479558039)
                ·
                  refine ⟨31515381347517387719337059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21010254231678258479558039 31515381347517387719337059)
                  ·
                    refine ⟨47273072021276081579005589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31515381347517387719337059 47273072021276081579005589)
                    ·
                      refine ⟨2215925250997316324015887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47273072021276081579005589 2215925250997316324015887)
                      ·
                        rfl

theorem cell23_4315499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 6].length) (baseStart_4315499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315499 prefixEnd_4315499 := by exact prefixLift 4315499
  have htrace : WordTrace (prefixWord ++ tailWord_4315499) baseStart_4315499 baseEnd_4315499 := by
    simpa [prefixWord, tailWord_4315499, baseEnd_4315499] using wordTrace_append hprefix tailTrace_4315499
  have hstable : (prefixWord ++ tailWord_4315499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315499).length < 2 ^ (prefixWord ++ tailWord_4315499).sum := by decide
  have hdescent : baseEnd_4315499 < baseStart_4315499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315503 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 5, 2, 2]
def baseStart_4315503 : Nat := 118140960795 + 4315503 * 2 ^ 59
def prefixEnd_4315503 : Nat := 4983230072969 + 3 ^ 40 * 4315503 * 2
def baseEnd_4315503 : Nat := 2215927304919934308365869

theorem tailTrace_4315503 : CollatzResearch.WordTrace tailWord_4315503 prefixEnd_4315503 2215927304919934308365869 := by
  unfold tailWord_4315503
  simp only [CollatzResearch.WordTrace]
  refine ⟨157399325284677135079615163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104932883523118090053076775 157399325284677135079615163)
  ·
    refine ⟨236098987927015702619422745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157399325284677135079615163 236098987927015702619422745)
    ·
      refine ⟨177074240945261776964567059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236098987927015702619422745 177074240945261776964567059)
      ·
        refine ⟨265611361417892665446850589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177074240945261776964567059 265611361417892665446850589)
        ·
          refine ⟨99604260531709749542568971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 265611361417892665446850589 99604260531709749542568971)
          ·
            refine ⟨149406390797564624313853457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99604260531709749542568971 149406390797564624313853457)
            ·
              refine ⟨112054793098173468235390093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149406390797564624313853457 112054793098173468235390093)
              ·
                refine ⟨42020547411815050588271285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112054793098173468235390093 42020547411815050588271285)
                ·
                  refine ⟨3939426319857660992650433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42020547411815050588271285 3939426319857660992650433)
                  ·
                    refine ⟨2954569739893245744487825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3939426319857660992650433 2954569739893245744487825)
                    ·
                      refine ⟨2215927304919934308365869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2954569739893245744487825 2215927304919934308365869)
                      ·
                        rfl

theorem cell23_4315503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 5, 2, 2].length) (baseStart_4315503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315503 prefixEnd_4315503 := by exact prefixLift 4315503
  have htrace : WordTrace (prefixWord ++ tailWord_4315503) baseStart_4315503 baseEnd_4315503 := by
    simpa [prefixWord, tailWord_4315503, baseEnd_4315503] using wordTrace_append hprefix tailTrace_4315503
  have hstable : (prefixWord ++ tailWord_4315503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315503).length < 2 ^ (prefixWord ++ tailWord_4315503).sum := by decide
  have hdescent : baseEnd_4315503 < baseStart_4315503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315523 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 5]
def baseStart_4315523 : Nat := 118140960795 + 4315523 * 2 ^ 59
def prefixEnd_4315523 : Nat := 4983230072969 + 3 ^ 40 * 4315523 * 2
def baseEnd_4315523 : Nat := 2215937574533024230115777

theorem tailTrace_4315523 : CollatzResearch.WordTrace tailWord_4315523 prefixEnd_4315523 2215937574533024230115777 := by
  unfold tailWord_4315523
  simp only [CollatzResearch.WordTrace]
  refine ⟨157400054744604678495343223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104933369829736452330228815 157400054744604678495343223)
  ·
    refine ⟨236100082116907017743014835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157400054744604678495343223 236100082116907017743014835)
    ·
      refine ⟨354150123175360526614522253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236100082116907017743014835 354150123175360526614522253)
      ·
        refine ⟨132806296190760197480445845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 354150123175360526614522253 132806296190760197480445845)
        ·
          refine ⟨6225295133941884256895899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 132806296190760197480445845 6225295133941884256895899)
          ·
            refine ⟨9337942700912826385343849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6225295133941884256895899 9337942700912826385343849)
            ·
              refine ⟨7003457025684619789007887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9337942700912826385343849 7003457025684619789007887)
              ·
                refine ⟨10505185538526929683511831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7003457025684619789007887 10505185538526929683511831)
                ·
                  refine ⟨15757778307790394525267747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10505185538526929683511831 15757778307790394525267747)
                  ·
                    refine ⟨23636667461685591787901621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15757778307790394525267747 23636667461685591787901621)
                    ·
                      refine ⟨2215937574533024230115777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23636667461685591787901621 2215937574533024230115777)
                      ·
                        rfl

theorem cell23_4315523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_4315523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315523 prefixEnd_4315523 := by exact prefixLift 4315523
  have htrace : WordTrace (prefixWord ++ tailWord_4315523) baseStart_4315523 baseEnd_4315523 := by
    simpa [prefixWord, tailWord_4315523, baseEnd_4315523] using wordTrace_append hprefix tailTrace_4315523
  have hstable : (prefixWord ++ tailWord_4315523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315523).length < 2 ^ (prefixWord ++ tailWord_4315523).sum := by decide
  have hdescent : baseEnd_4315523 < baseStart_4315523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315588 : List Nat := [2, 3, 3, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_4315588 : Nat := 118140960795 + 4315588 * 2 ^ 59
def prefixEnd_4315588 : Nat := 4983230072969 + 3 ^ 40 * 4315588 * 2
def baseEnd_4315588 : Nat := 2215970950775566475802979

theorem tailTrace_4315588 : CollatzResearch.WordTrace tailWord_4315588 prefixEnd_4315588 2215970950775566475802979 := by
  unfold tailWord_4315588
  simp only [CollatzResearch.WordTrace]
  refine ⟨78701212744684597298229709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104934950326246129730972945 78701212744684597298229709)
  ·
    refine ⟨29512954779256723986836141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78701212744684597298229709 29512954779256723986836141)
    ·
      refine ⟨11067358042221271495063553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29512954779256723986836141 11067358042221271495063553)
      ·
        refine ⟨8300518531665953621297665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11067358042221271495063553 8300518531665953621297665)
        ·
          refine ⟨6225388898749465215973249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8300518531665953621297665 6225388898749465215973249)
          ·
            refine ⟨4669041674062098911979937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6225388898749465215973249 4669041674062098911979937)
            ·
              refine ⟨3501781255546574183984953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4669041674062098911979937 3501781255546574183984953)
              ·
                refine ⟨2626335941659930637988715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3501781255546574183984953 2626335941659930637988715)
                ·
                  refine ⟨3939503912489895956983073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2626335941659930637988715 3939503912489895956983073)
                  ·
                    refine ⟨2954627934367421967737305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3939503912489895956983073 2954627934367421967737305)
                    ·
                      refine ⟨2215970950775566475802979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2954627934367421967737305 2215970950775566475802979)
                      ·
                        rfl

theorem cell23_4315588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_4315588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315588 prefixEnd_4315588 := by exact prefixLift 4315588
  have htrace : WordTrace (prefixWord ++ tailWord_4315588) baseStart_4315588 baseEnd_4315588 := by
    simpa [prefixWord, tailWord_4315588, baseEnd_4315588] using wordTrace_append hprefix tailTrace_4315588
  have hstable : (prefixWord ++ tailWord_4315588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315588).length < 2 ^ (prefixWord ++ tailWord_4315588).sum := by decide
  have hdescent : baseEnd_4315588 < baseStart_4315588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315610 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2]
def baseStart_4315610 : Nat := 118140960795 + 4315610 * 2 ^ 59
def prefixEnd_4315610 : Nat := 4983230072969 + 3 ^ 40 * 4315610 * 2
def baseEnd_4315610 : Nat := 2215982247349965389727877

theorem tailTrace_4315610 : CollatzResearch.WordTrace tailWord_4315610 prefixEnd_4315610 2215982247349965389727877 := by
  unfold tailWord_4315610
  simp only [CollatzResearch.WordTrace]
  refine ⟨39350806973822373088440071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104935485263526328235840189 39350806973822373088440071)
  ·
    refine ⟨59026210460733559632660107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39350806973822373088440071 59026210460733559632660107)
    ·
      refine ⟨88539315691100339448990161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59026210460733559632660107 88539315691100339448990161)
      ·
        refine ⟨66404486768325254586742621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88539315691100339448990161 66404486768325254586742621)
        ·
          refine ⟨24901682538121970470028483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66404486768325254586742621 24901682538121970470028483)
          ·
            refine ⟨37352523807182955705042725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24901682538121970470028483 37352523807182955705042725)
            ·
              refine ⟨7003598213846804194695511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37352523807182955705042725 7003598213846804194695511)
              ·
                refine ⟨10505397320770206292043267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7003598213846804194695511 10505397320770206292043267)
                ·
                  refine ⟨15758095981155309438064901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10505397320770206292043267 15758095981155309438064901)
                  ·
                    refine ⟨2954642996466620519637169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15758095981155309438064901 2954642996466620519637169)
                    ·
                      refine ⟨2215982247349965389727877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2954642996466620519637169 2215982247349965389727877)
                      ·
                        rfl

theorem cell23_4315610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_4315610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315610 prefixEnd_4315610 := by exact prefixLift 4315610
  have htrace : WordTrace (prefixWord ++ tailWord_4315610) baseStart_4315610 baseEnd_4315610 := by
    simpa [prefixWord, tailWord_4315610, baseEnd_4315610] using wordTrace_append hprefix tailTrace_4315610
  have hstable : (prefixWord ++ tailWord_4315610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315610).length < 2 ^ (prefixWord ++ tailWord_4315610).sum := by decide
  have hdescent : baseEnd_4315610 < baseStart_4315610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315613 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_4315613 : Nat := 118140960795 + 4315613 * 2 ^ 59
def prefixEnd_4315613 : Nat := 4983230072969 + 3 ^ 40 * 4315613 * 2
def baseEnd_4315613 : Nat := 2215983787791928877990363

theorem tailTrace_4315613 : CollatzResearch.WordTrace tailWord_4315613 prefixEnd_4315613 2215983787791928877990363 := by
  unfold tailWord_4315613
  simp only [CollatzResearch.WordTrace]
  refine ⟨157403337314278623866119493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104935558209519082577412995 157403337314278623866119493)
  ·
    refine ⟨29513125746427241974897405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157403337314278623866119493 29513125746427241974897405)
    ·
      refine ⟨11067422154910215740586527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29513125746427241974897405 11067422154910215740586527)
      ·
        refine ⟨16601133232365323610879791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11067422154910215740586527 16601133232365323610879791)
        ·
          refine ⟨24901699848547985416319687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16601133232365323610879791 24901699848547985416319687)
          ·
            refine ⟨37352549772821978124479531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24901699848547985416319687 37352549772821978124479531)
            ·
              refine ⟨56028824659232967186719297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37352549772821978124479531 56028824659232967186719297)
              ·
                refine ⟨42021618494424725390039473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56028824659232967186719297 42021618494424725390039473)
                ·
                  refine ⟨31516213870818544042529605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42021618494424725390039473 31516213870818544042529605)
                  ·
                    refine ⟨5909290100778477007974301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31516213870818544042529605 5909290100778477007974301)
                    ·
                      refine ⟨2215983787791928877990363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5909290100778477007974301 2215983787791928877990363)
                      ·
                        rfl

theorem cell23_4315613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_4315613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315613 prefixEnd_4315613 := by exact prefixLift 4315613
  have htrace : WordTrace (prefixWord ++ tailWord_4315613) baseStart_4315613 baseEnd_4315613 := by
    simpa [prefixWord, tailWord_4315613, baseEnd_4315613] using wordTrace_append hprefix tailTrace_4315613
  have hstable : (prefixWord ++ tailWord_4315613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315613).length < 2 ^ (prefixWord ++ tailWord_4315613).sum := by decide
  have hdescent : baseEnd_4315613 < baseStart_4315613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315616 : List Nat := [2, 1, 1, 3, 1, 1, 5, 2, 7]
def baseStart_4315616 : Nat := 118140960795 + 4315616 * 2 ^ 59
def prefixEnd_4315616 : Nat := 4983230072969 + 3 ^ 40 * 4315616 * 2
def baseEnd_4315616 : Nat := 246220592025988040694761

theorem tailTrace_4315616 : CollatzResearch.WordTrace tailWord_4315616 prefixEnd_4315616 246220592025988040694761 := by
  unfold tailWord_4315616
  simp only [CollatzResearch.WordTrace]
  refine ⟨78701723366633877689239351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104935631155511836918985801 78701723366633877689239351)
  ·
    refine ⟨118052585049950816533859027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78701723366633877689239351 118052585049950816533859027)
    ·
      refine ⟨177078877574926224800788541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118052585049950816533859027 177078877574926224800788541)
      ·
        refine ⟨66404579090597334300295703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177078877574926224800788541 66404579090597334300295703)
        ·
          refine ⟨99606868635896001450443555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66404579090597334300295703 99606868635896001450443555)
          ·
            refine ⟨149410302953844002175665333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99606868635896001450443555 149410302953844002175665333)
            ·
              refine ⟨14007215901922875203968625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 149410302953844002175665333 14007215901922875203968625)
              ·
                refine ⟨10505411926442156402976469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14007215901922875203968625 10505411926442156402976469)
                ·
                  refine ⟨246220592025988040694761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10505411926442156402976469 246220592025988040694761)
                  ·
                    rfl

theorem cell23_4315616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 7].length) (baseStart_4315616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315616 prefixEnd_4315616 := by exact prefixLift 4315616
  have htrace : WordTrace (prefixWord ++ tailWord_4315616) baseStart_4315616 baseEnd_4315616 := by
    simpa [prefixWord, tailWord_4315616, baseEnd_4315616] using wordTrace_append hprefix tailTrace_4315616
  have hstable : (prefixWord ++ tailWord_4315616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315616).length < 2 ^ (prefixWord ++ tailWord_4315616).sum := by decide
  have hdescent : baseEnd_4315616 < baseStart_4315616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315653 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 1, 7, 2]
def baseStart_4315653 : Nat := 118140960795 + 4315653 * 2 ^ 59
def prefixEnd_4315653 : Nat := 4983230072969 + 3 ^ 40 * 4315653 * 2
def baseEnd_4315653 : Nat := 2216004327018108721490179

theorem tailTrace_4315653 : CollatzResearch.WordTrace tailWord_4315653 prefixEnd_4315653 2216004327018108721490179 := by
  unfold tailWord_4315653
  simp only [CollatzResearch.WordTrace]
  refine ⟨157404796234133710697575613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104936530822755807131717075 157404796234133710697575613)
  ·
    refine ⟨59026798587800141511590855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157404796234133710697575613 59026798587800141511590855)
    ·
      refine ⟨88540197881700212267386283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59026798587800141511590855 88540197881700212267386283)
      ·
        refine ⟨132810296822550318401079425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88540197881700212267386283 132810296822550318401079425)
        ·
          refine ⟨99607722616912738800809569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132810296822550318401079425 99607722616912738800809569)
          ·
            refine ⟨74705791962684554100607177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99607722616912738800809569 74705791962684554100607177)
            ·
              refine ⟨56029343972013415575455383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74705791962684554100607177 56029343972013415575455383)
              ·
                refine ⟨84044015958020123363183075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56029343972013415575455383 84044015958020123363183075)
                ·
                  refine ⟨126066023937030185044774613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84044015958020123363183075 126066023937030185044774613)
                  ·
                    refine ⟨2954672436024144961986905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 126066023937030185044774613 2954672436024144961986905)
                    ·
                      refine ⟨2216004327018108721490179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2954672436024144961986905 2216004327018108721490179)
                      ·
                        rfl

theorem cell23_4315653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 7, 2].length) (baseStart_4315653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315653 prefixEnd_4315653 := by exact prefixLift 4315653
  have htrace : WordTrace (prefixWord ++ tailWord_4315653) baseStart_4315653 baseEnd_4315653 := by
    simpa [prefixWord, tailWord_4315653, baseEnd_4315653] using wordTrace_append hprefix tailTrace_4315653
  have hstable : (prefixWord ++ tailWord_4315653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315653).length < 2 ^ (prefixWord ++ tailWord_4315653).sum := by decide
  have hdescent : baseEnd_4315653 < baseStart_4315653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315656 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_4315656 : Nat := 118140960795 + 4315656 * 2 ^ 59
def prefixEnd_4315656 : Nat := 4983230072969 + 3 ^ 40 * 4315656 * 2
def baseEnd_4315656 : Nat := 2216005867460072209752665

theorem tailTrace_4315656 : CollatzResearch.WordTrace tailWord_4315656 prefixEnd_4315656 2216005867460072209752665 := by
  unfold tailWord_4315656
  simp only [CollatzResearch.WordTrace]
  refine ⟨78702452826561421104967411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104936603768748561473289881 78702452826561421104967411)
  ·
    refine ⟨118053679239842131657451117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78702452826561421104967411 118053679239842131657451117)
    ·
      refine ⟨44270129714940799371544169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118053679239842131657451117 44270129714940799371544169)
      ·
        refine ⟨33202597286205599528658127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44270129714940799371544169 33202597286205599528658127)
        ·
          refine ⟨49803895929308399292987191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33202597286205599528658127 49803895929308399292987191)
          ·
            refine ⟨74705843893962598939480787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49803895929308399292987191 74705843893962598939480787)
            ·
              refine ⟨112058765840943898409221181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74705843893962598939480787 112058765840943898409221181)
              ·
                refine ⟨42022037190353961903457943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112058765840943898409221181 42022037190353961903457943)
                ·
                  refine ⟨63033055785530942855186915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42022037190353961903457943 63033055785530942855186915)
                  ·
                    refine ⟨94549583678296414282780373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63033055785530942855186915 94549583678296414282780373)
                    ·
                      refine ⟨2216005867460072209752665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94549583678296414282780373 2216005867460072209752665)
                      ·
                        rfl

theorem cell23_4315656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_4315656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315656 prefixEnd_4315656 := by exact prefixLift 4315656
  have htrace : WordTrace (prefixWord ++ tailWord_4315656) baseStart_4315656 baseEnd_4315656 := by
    simpa [prefixWord, tailWord_4315656, baseEnd_4315656] using wordTrace_append hprefix tailTrace_4315656
  have hstable : (prefixWord ++ tailWord_4315656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315656).length < 2 ^ (prefixWord ++ tailWord_4315656).sum := by decide
  have hdescent : baseEnd_4315656 < baseStart_4315656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315661 : List Nat := [1, 7, 1, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_4315661 : Nat := 118140960795 + 4315661 * 2 ^ 59
def prefixEnd_4315661 : Nat := 4983230072969 + 3 ^ 40 * 4315661 * 2
def baseEnd_4315661 : Nat := 2216008434863344690190143

theorem tailTrace_4315661 : CollatzResearch.WordTrace tailWord_4315661 prefixEnd_4315661 2216008434863344690190143 := by
  unfold tailWord_4315661
  simp only [CollatzResearch.WordTrace]
  refine ⟨157405088018104728063866837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104936725345403152042577891 157405088018104728063866837)
  ·
    refine ⟨3689181750424329563996879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 157405088018104728063866837 3689181750424329563996879)
    ·
      refine ⟨5533772625636494345995319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3689181750424329563996879 5533772625636494345995319)
      ·
        refine ⟨8300658938454741518992979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5533772625636494345995319 8300658938454741518992979)
        ·
          refine ⟨12450988407682112278489469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8300658938454741518992979 12450988407682112278489469)
          ·
            refine ⟨4669120652880792104433551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12450988407682112278489469 4669120652880792104433551)
            ·
              refine ⟨7003680979321188156650327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4669120652880792104433551 7003680979321188156650327)
              ·
                refine ⟨10505521468981782234975491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7003680979321188156650327 10505521468981782234975491)
                ·
                  refine ⟨15758282203472673352463237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10505521468981782234975491 15758282203472673352463237)
                  ·
                    refine ⟨2954677913151126253586857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15758282203472673352463237 2954677913151126253586857)
                    ·
                      refine ⟨2216008434863344690190143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2954677913151126253586857 2216008434863344690190143)
                      ·
                        rfl

theorem cell23_4315661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_4315661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315661 prefixEnd_4315661 := by exact prefixLift 4315661
  have htrace : WordTrace (prefixWord ++ tailWord_4315661) baseStart_4315661 baseEnd_4315661 := by
    simpa [prefixWord, tailWord_4315661, baseEnd_4315661] using wordTrace_append hprefix tailTrace_4315661
  have hstable : (prefixWord ++ tailWord_4315661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315661).length < 2 ^ (prefixWord ++ tailWord_4315661).sum := by decide
  have hdescent : baseEnd_4315661 < baseStart_4315661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315683 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 4]
def baseStart_4315683 : Nat := 118140960795 + 4315683 * 2 ^ 59
def prefixEnd_4315683 : Nat := 4983230072969 + 3 ^ 40 * 4315683 * 2
def baseEnd_4315683 : Nat := 2216019731437743604115041

theorem tailTrace_4315683 : CollatzResearch.WordTrace tailWord_4315683 prefixEnd_4315683 2216019731437743604115041 := by
  unfold tailWord_4315683
  simp only [CollatzResearch.WordTrace]
  refine ⟨157405890424025025821167703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104937260282683350547445135 157405890424025025821167703)
  ·
    refine ⟨236108835636037538731751555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157405890424025025821167703 236108835636037538731751555)
    ·
      refine ⟨354163253454056308097627333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236108835636037538731751555 354163253454056308097627333)
      ·
        refine ⟨66405610022635557768305125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 354163253454056308097627333 66405610022635557768305125)
        ·
          refine ⟨12451051879244167081557211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66405610022635557768305125 12451051879244167081557211)
          ·
            refine ⟨18676577818866250622335817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12451051879244167081557211 18676577818866250622335817)
            ·
              refine ⟨14007433364149687966751863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18676577818866250622335817 14007433364149687966751863)
              ·
                refine ⟨21011150046224531950127795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14007433364149687966751863 21011150046224531950127795)
                ·
                  refine ⟨31516725069336797925191693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21011150046224531950127795 31516725069336797925191693)
                  ·
                    refine ⟨11818771901001299221946885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31516725069336797925191693 11818771901001299221946885)
                    ·
                      refine ⟨2216019731437743604115041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11818771901001299221946885 2216019731437743604115041)
                      ·
                        rfl

theorem cell23_4315683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_4315683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315683 prefixEnd_4315683 := by exact prefixLift 4315683
  have htrace : WordTrace (prefixWord ++ tailWord_4315683) baseStart_4315683 baseEnd_4315683 := by
    simpa [prefixWord, tailWord_4315683, baseEnd_4315683] using wordTrace_append hprefix tailTrace_4315683
  have hstable : (prefixWord ++ tailWord_4315683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315683).length < 2 ^ (prefixWord ++ tailWord_4315683).sum := by decide
  have hdescent : baseEnd_4315683 < baseStart_4315683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315684 : List Nat := [2, 3, 1, 5, 1, 2, 1, 3, 5]
def baseStart_4315684 : Nat := 118140960795 + 4315684 * 2 ^ 59
def prefixEnd_4315684 : Nat := 4983230072969 + 3 ^ 40 * 4315684 * 2
def baseEnd_4315684 : Nat := 246224471657599788911393

theorem tailTrace_4315684 : CollatzResearch.WordTrace tailWord_4315684 prefixEnd_4315684 246224471657599788911393 := by
  unfold tailWord_4315684
  simp only [CollatzResearch.WordTrace]
  refine ⟨78702963448510701495977053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104937284598014268661302737 78702963448510701495977053)
  ·
    refine ⟨29513611293191513060991395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78702963448510701495977053 29513611293191513060991395)
    ·
      refine ⟨44270416939787269591487093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29513611293191513060991395 44270416939787269591487093)
      ·
        refine ⟨4150351588105056524201915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 44270416939787269591487093 4150351588105056524201915)
        ·
          refine ⟨6225527382157584786302873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4150351588105056524201915 6225527382157584786302873)
          ·
            refine ⟨4669145536618188589727155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6225527382157584786302873 4669145536618188589727155)
            ·
              refine ⟨7003718304927282884590733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4669145536618188589727155 7003718304927282884590733)
              ·
                refine ⟨2626394364347731081721525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7003718304927282884590733 2626394364347731081721525)
                ·
                  refine ⟨246224471657599788911393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2626394364347731081721525 246224471657599788911393)
                  ·
                    rfl

theorem cell23_4315684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_4315684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315684 prefixEnd_4315684 := by exact prefixLift 4315684
  have htrace : WordTrace (prefixWord ++ tailWord_4315684) baseStart_4315684 baseEnd_4315684 := by
    simpa [prefixWord, tailWord_4315684, baseEnd_4315684] using wordTrace_append hprefix tailTrace_4315684
  have hstable : (prefixWord ++ tailWord_4315684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315684).length < 2 ^ (prefixWord ++ tailWord_4315684).sum := by decide
  have hdescent : baseEnd_4315684 < baseStart_4315684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315696 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 6]
def baseStart_4315696 : Nat := 118140960795 + 4315696 * 2 ^ 59
def prefixEnd_4315696 : Nat := 4983230072969 + 3 ^ 40 * 4315696 * 2
def baseEnd_4315696 : Nat := 2216026406686252053252481

theorem tailTrace_4315696 : CollatzResearch.WordTrace tailWord_4315696 prefixEnd_4315696 2216026406686252053252481 := by
  unfold tailWord_4315696
  simp only [CollatzResearch.WordTrace]
  refine ⟨78703182286488964520695471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104937576381985286027593961 78703182286488964520695471)
  ·
    refine ⟨118054773429733446781043207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78703182286488964520695471 118054773429733446781043207)
    ·
      refine ⟨177082160144600170171564811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118054773429733446781043207 177082160144600170171564811)
      ·
        refine ⟨265623240216900255257347217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177082160144600170171564811 265623240216900255257347217)
        ·
          refine ⟨199217430162675191443010413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265623240216900255257347217 199217430162675191443010413)
          ·
            refine ⟨74706536311003196791128905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199217430162675191443010413 74706536311003196791128905)
            ·
              refine ⟨56029902233252397593346679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74706536311003196791128905 56029902233252397593346679)
              ·
                refine ⟨84044853349878596390020019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56029902233252397593346679 84044853349878596390020019)
                ·
                  refine ⟨126067280024817894585030029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84044853349878596390020019 126067280024817894585030029)
                  ·
                    refine ⟨47275230009306710469386261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 126067280024817894585030029 47275230009306710469386261)
                    ·
                      refine ⟨2216026406686252053252481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47275230009306710469386261 2216026406686252053252481)
                      ·
                        rfl

theorem cell23_4315696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_4315696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315696 prefixEnd_4315696 := by exact prefixLift 4315696
  have htrace : WordTrace (prefixWord ++ tailWord_4315696) baseStart_4315696 baseEnd_4315696 := by
    simpa [prefixWord, tailWord_4315696, baseEnd_4315696] using wordTrace_append hprefix tailTrace_4315696
  have hstable : (prefixWord ++ tailWord_4315696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315696).length < 2 ^ (prefixWord ++ tailWord_4315696).sum := by decide
  have hdescent : baseEnd_4315696 < baseStart_4315696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315733 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 2, 5, 3]
def baseStart_4315733 : Nat := 118140960795 + 4315733 * 2 ^ 59
def prefixEnd_4315733 : Nat := 4983230072969 + 3 ^ 40 * 4315733 * 2
def baseEnd_4315733 : Nat := 2216045405470468408489811

theorem tailTrace_4315733 : CollatzResearch.WordTrace tailWord_4315733 prefixEnd_4315733 2216045405470468408489811 := by
  unfold tailWord_4315733
  simp only [CollatzResearch.WordTrace]
  refine ⟨157407714073843884360487853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104938476049229256240325235 157407714073843884360487853)
  ·
    refine ⟨59027892777691456635182945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157407714073843884360487853 59027892777691456635182945)
    ·
      refine ⟨44270919583268592476387209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59027892777691456635182945 44270919583268592476387209)
      ·
        refine ⟨33203189687451444357290407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44270919583268592476387209 33203189687451444357290407)
        ·
          refine ⟨49804784531177166535935611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33203189687451444357290407 49804784531177166535935611)
          ·
            refine ⟨74707176796765749803903417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49804784531177166535935611 74707176796765749803903417)
            ·
              refine ⟨56030382597574312352927563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74707176796765749803903417 56030382597574312352927563)
              ·
                refine ⟨84045573896361468529391345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56030382597574312352927563 84045573896361468529391345)
                ·
                  refine ⟨63034180422271101397043509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84045573896361468529391345 63034180422271101397043509)
                  ·
                    refine ⟨5909454414587915755972829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63034180422271101397043509 5909454414587915755972829)
                    ·
                      refine ⟨2216045405470468408489811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5909454414587915755972829 2216045405470468408489811)
                      ·
                        rfl

theorem cell23_4315733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_4315733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315733 prefixEnd_4315733 := by exact prefixLift 4315733
  have htrace : WordTrace (prefixWord ++ tailWord_4315733) baseStart_4315733 baseEnd_4315733 := by
    simpa [prefixWord, tailWord_4315733, baseEnd_4315733] using wordTrace_append hprefix tailTrace_4315733
  have hstable : (prefixWord ++ tailWord_4315733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315733).length < 2 ^ (prefixWord ++ tailWord_4315733).sum := by decide
  have hdescent : baseEnd_4315733 < baseStart_4315733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315790 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_4315790 : Nat := 118140960795 + 4315790 * 2 ^ 59
def prefixEnd_4315790 : Nat := 4983230072969 + 3 ^ 40 * 4315790 * 2
def baseEnd_4315790 : Nat := 2216074673867774685477049

theorem tailTrace_4315790 : CollatzResearch.WordTrace tailWord_4315790 prefixEnd_4315790 2216074673867774685477049 := by
  unfold tailWord_4315790
  simp only [CollatzResearch.WordTrace]
  refine ⟨19676224129329672886914103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104939862023091588730208549 19676224129329672886914103)
  ·
    refine ⟨29514336193994509330371155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19676224129329672886914103 29514336193994509330371155)
    ·
      refine ⟨44271504290991763995556733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29514336193994509330371155 44271504290991763995556733)
      ·
        refine ⟨16601814109121911498333775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44271504290991763995556733 16601814109121911498333775)
        ·
          refine ⟨24902721163682867247500663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16601814109121911498333775 24902721163682867247500663)
          ·
            refine ⟨37354081745524300871250995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24902721163682867247500663 37354081745524300871250995)
            ·
              refine ⟨56031122618286451306876493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37354081745524300871250995 56031122618286451306876493)
              ·
                refine ⟨21011670981857419240078685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56031122618286451306876493 21011670981857419240078685)
                ·
                  refine ⟨7879376618196532215029507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21011670981857419240078685 7879376618196532215029507)
                  ·
                    refine ⟨11819064927294798322544261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7879376618196532215029507 11819064927294798322544261)
                    ·
                      refine ⟨2216074673867774685477049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11819064927294798322544261 2216074673867774685477049)
                      ·
                        rfl

theorem cell23_4315790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_4315790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315790 prefixEnd_4315790 := by exact prefixLift 4315790
  have htrace : WordTrace (prefixWord ++ tailWord_4315790) baseStart_4315790 baseEnd_4315790 := by
    simpa [prefixWord, tailWord_4315790, baseEnd_4315790] using wordTrace_append hprefix tailTrace_4315790
  have hstable : (prefixWord ++ tailWord_4315790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315790).length < 2 ^ (prefixWord ++ tailWord_4315790).sum := by decide
  have hdescent : baseEnd_4315790 < baseStart_4315790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315794 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_4315794 : Nat := 118140960795 + 4315794 * 2 ^ 59
def prefixEnd_4315794 : Nat := 4983230072969 + 3 ^ 40 * 4315794 * 2
def baseEnd_4315794 : Nat := 2216076727790392669827031

theorem tailTrace_4315794 : CollatzResearch.WordTrace tailWord_4315794 prefixEnd_4315794 2216076727790392669827031 := by
  unfold tailWord_4315794
  simp only [CollatzResearch.WordTrace]
  refine ⟨39352484731655722944614609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104939959284415261185638957 39352484731655722944614609)
  ·
    refine ⟨29514363548741792208460957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39352484731655722944614609 29514363548741792208460957)
    ·
      refine ⟨11067886330778172078172859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29514363548741792208460957 11067886330778172078172859)
      ·
        refine ⟨16601829496167258117259289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11067886330778172078172859 16601829496167258117259289)
        ·
          refine ⟨12451372122125443587944467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16601829496167258117259289 12451372122125443587944467)
          ·
            refine ⟨18677058183188165381916701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12451372122125443587944467 18677058183188165381916701)
            ·
              refine ⟨7003896818695562018218763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18677058183188165381916701 7003896818695562018218763)
              ·
                refine ⟨10505845228043343027328145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7003896818695562018218763 10505845228043343027328145)
                ·
                  refine ⟨7879383921032507270496109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10505845228043343027328145 7879383921032507270496109)
                  ·
                    refine ⟨2954768970387190226436041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7879383921032507270496109 2954768970387190226436041)
                    ·
                      refine ⟨2216076727790392669827031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2954768970387190226436041 2216076727790392669827031)
                      ·
                        rfl

theorem cell23_4315794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_4315794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315794 prefixEnd_4315794 := by exact prefixLift 4315794
  have htrace : WordTrace (prefixWord ++ tailWord_4315794) baseStart_4315794 baseEnd_4315794 := by
    simpa [prefixWord, tailWord_4315794, baseEnd_4315794] using wordTrace_append hprefix tailTrace_4315794
  have hstable : (prefixWord ++ tailWord_4315794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315794).length < 2 ^ (prefixWord ++ tailWord_4315794).sum := by decide
  have hdescent : baseEnd_4315794 < baseStart_4315794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315800 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 4, 4]
def baseStart_4315800 : Nat := 118140960795 + 4315800 * 2 ^ 59
def prefixEnd_4315800 : Nat := 4983230072969 + 3 ^ 40 * 4315800 * 2
def baseEnd_4315800 : Nat := 738693269558106548784001

theorem tailTrace_4315800 : CollatzResearch.WordTrace tailWord_4315800 prefixEnd_4315800 738693269558106548784001 := by
  unfold tailWord_4315800
  simp only [CollatzResearch.WordTrace]
  refine ⟨78705078882300577401588427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104940105176400769868784569 78705078882300577401588427)
  ·
    refine ⟨118057618323450866102382641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78705078882300577401588427 118057618323450866102382641)
    ·
      refine ⟨88543213742588149576786981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118057618323450866102382641 88543213742588149576786981)
      ·
        refine ⟨16601852576735278045647559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 88543213742588149576786981 16601852576735278045647559)
        ·
          refine ⟨24902778865102917068471339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16601852576735278045647559 24902778865102917068471339)
          ·
            refine ⟨37354168297654375602707009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24902778865102917068471339 37354168297654375602707009)
            ·
              refine ⟨28015626223240781702030257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37354168297654375602707009 28015626223240781702030257)
              ·
                refine ⟨21011719667430586276522693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28015626223240781702030257 21011719667430586276522693)
                ·
                  refine ⟨3939697437643234926848005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21011719667430586276522693 3939697437643234926848005)
                  ·
                    refine ⟨738693269558106548784001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3939697437643234926848005 738693269558106548784001)
                    ·
                      rfl

theorem cell23_4315800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_4315800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315800 prefixEnd_4315800 := by exact prefixLift 4315800
  have htrace : WordTrace (prefixWord ++ tailWord_4315800) baseStart_4315800 baseEnd_4315800 := by
    simpa [prefixWord, tailWord_4315800, baseEnd_4315800] using wordTrace_append hprefix tailTrace_4315800
  have hstable : (prefixWord ++ tailWord_4315800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315800).length < 2 ^ (prefixWord ++ tailWord_4315800).sum := by decide
  have hdescent : baseEnd_4315800 < baseStart_4315800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315804 : List Nat := [2, 2, 3, 2, 2, 3, 2, 1, 1, 5]
def baseStart_4315804 : Nat := 118140960795 + 4315804 * 2 ^ 59
def prefixEnd_4315804 : Nat := 4983230072969 + 3 ^ 40 * 4315804 * 2
def baseEnd_4315804 : Nat := 738693954198979210233995

theorem tailTrace_4315804 : CollatzResearch.WordTrace tailWord_4315804 prefixEnd_4315804 738693954198979210233995 := by
  unfold tailWord_4315804
  simp only [CollatzResearch.WordTrace]
  refine ⟨78705151828293331743161233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104940202437724442324214977 78705151828293331743161233)
  ·
    refine ⟨59028863871219998807370925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78705151828293331743161233 59028863871219998807370925)
    ·
      refine ⟨22135823951707499552764097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59028863871219998807370925 22135823951707499552764097)
      ·
        refine ⟨16601867963780624664573073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22135823951707499552764097 16601867963780624664573073)
        ·
          refine ⟨12451400972835468498429805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16601867963780624664573073 12451400972835468498429805)
          ·
            refine ⟨4669275364813300686911177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12451400972835468498429805 4669275364813300686911177)
            ·
              refine ⟨3501956523609975515183383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4669275364813300686911177 3501956523609975515183383)
              ·
                refine ⟨5252934785414963272775075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3501956523609975515183383 5252934785414963272775075)
                ·
                  refine ⟨7879402178122444909162613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5252934785414963272775075 7879402178122444909162613)
                  ·
                    refine ⟨738693954198979210233995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7879402178122444909162613 738693954198979210233995)
                    ·
                      rfl

theorem cell23_4315804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_4315804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315804 prefixEnd_4315804 := by exact prefixLift 4315804
  have htrace : WordTrace (prefixWord ++ tailWord_4315804) baseStart_4315804 baseEnd_4315804 := by
    simpa [prefixWord, tailWord_4315804, baseEnd_4315804] using wordTrace_append hprefix tailTrace_4315804
  have hstable : (prefixWord ++ tailWord_4315804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315804).length < 2 ^ (prefixWord ++ tailWord_4315804).sum := by decide
  have hdescent : baseEnd_4315804 < baseStart_4315804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315837 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 1, 2, 4]
def baseStart_4315837 : Nat := 118140960795 + 4315837 * 2 ^ 59
def prefixEnd_4315837 : Nat := 4983230072969 + 3 ^ 40 * 4315837 * 2
def baseEnd_4315837 : Nat := 2216098807458536001589333

theorem tailTrace_4315837 : CollatzResearch.WordTrace tailWord_4315837 prefixEnd_4315837 2216098807458536001589333 := by
  unfold tailWord_4315837
  simp only [CollatzResearch.WordTrace]
  refine ⟨157411507265467110122273765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104941004843644740081515843 157411507265467110122273765)
  ·
    refine ⟨29514657612275083147926331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157411507265467110122273765 29514657612275083147926331)
    ·
      refine ⟨44271986418412624721889497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29514657612275083147926331 44271986418412624721889497)
      ·
        refine ⟨33203989813809468541417123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44271986418412624721889497 33203989813809468541417123)
        ·
          refine ⟨49805984720714202812125685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33203989813809468541417123 49805984720714202812125685)
          ·
            refine ⟨4669311067566956513636783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 49805984720714202812125685 4669311067566956513636783)
            ·
              refine ⟨7003966601350434770455175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4669311067566956513636783 7003966601350434770455175)
              ·
                refine ⟨10505949902025652155682763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7003966601350434770455175 10505949902025652155682763)
                ·
                  refine ⟨15758924853038478233524145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10505949902025652155682763 15758924853038478233524145)
                  ·
                    refine ⟨11819193639778858675143109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15758924853038478233524145 11819193639778858675143109)
                    ·
                      refine ⟨2216098807458536001589333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11819193639778858675143109 2216098807458536001589333)
                      ·
                        rfl

theorem cell23_4315837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_4315837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315837 prefixEnd_4315837 := by exact prefixLift 4315837
  have htrace : WordTrace (prefixWord ++ tailWord_4315837) baseStart_4315837 baseEnd_4315837 := by
    simpa [prefixWord, tailWord_4315837, baseEnd_4315837] using wordTrace_append hprefix tailTrace_4315837
  have hstable : (prefixWord ++ tailWord_4315837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315837).length < 2 ^ (prefixWord ++ tailWord_4315837).sum := by decide
  have hdescent : baseEnd_4315837 < baseStart_4315837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315841 : List Nat := [1, 2, 6, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4315841 : Nat := 118140960795 + 4315841 * 2 ^ 59
def prefixEnd_4315841 : Nat := 4983230072969 + 3 ^ 40 * 4315841 * 2
def baseEnd_4315841 : Nat := 2216100861381153985939315

theorem tailTrace_4315841 : CollatzResearch.WordTrace tailWord_4315841 prefixEnd_4315841 2216100861381153985939315 := by
  unfold tailWord_4315841
  simp only [CollatzResearch.WordTrace]
  refine ⟨157411653157452618805419377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104941102104968412536946251 157411653157452618805419377)
  ·
    refine ⟨118058739868089464104064533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157411653157452618805419377 118058739868089464104064533)
    ·
      refine ⟨5534003431316693629878025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 118058739868089464104064533 5534003431316693629878025)
      ·
        refine ⟨4150502573487520222408519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5534003431316693629878025 4150502573487520222408519)
        ·
          refine ⟨6225753860231280333612779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4150502573487520222408519 6225753860231280333612779)
          ·
            refine ⟨9338630790346920500419169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6225753860231280333612779 9338630790346920500419169)
            ·
              refine ⟨7003973092760190375314377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9338630790346920500419169 7003973092760190375314377)
              ·
                refine ⟨5252979819570142781485783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7003973092760190375314377 5252979819570142781485783)
                ·
                  refine ⟨7879469729355214172228675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5252979819570142781485783 7879469729355214172228675)
                  ·
                    refine ⟨11819204594032821258343013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7879469729355214172228675 11819204594032821258343013)
                    ·
                      refine ⟨2216100861381153985939315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11819204594032821258343013 2216100861381153985939315)
                      ·
                        rfl

theorem cell23_4315841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4315841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315841 prefixEnd_4315841 := by exact prefixLift 4315841
  have htrace : WordTrace (prefixWord ++ tailWord_4315841) baseStart_4315841 baseEnd_4315841 := by
    simpa [prefixWord, tailWord_4315841, baseEnd_4315841] using wordTrace_append hprefix tailTrace_4315841
  have hstable : (prefixWord ++ tailWord_4315841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315841).length < 2 ^ (prefixWord ++ tailWord_4315841).sum := by decide
  have hdescent : baseEnd_4315841 < baseStart_4315841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315844 : List Nat := [2, 3, 3, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_4315844 : Nat := 118140960795 + 4315844 * 2 ^ 59
def prefixEnd_4315844 : Nat := 4983230072969 + 3 ^ 40 * 4315844 * 2
def baseEnd_4315844 : Nat := 2216102401823117474201801

theorem tailTrace_4315844 : CollatzResearch.WordTrace tailWord_4315844 prefixEnd_4315844 2216102401823117474201801 := by
  unfold tailWord_4315844
  simp only [CollatzResearch.WordTrace]
  refine ⟨78705881288220875158889293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104941175050961166878519057 78705881288220875158889293)
  ·
    refine ⟨29514705483082828184583485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78705881288220875158889293 29514705483082828184583485)
    ·
      refine ⟨11068014556156060569218807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29514705483082828184583485 11068014556156060569218807)
      ·
        refine ⟨16602021834234090853828211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11068014556156060569218807 16602021834234090853828211)
        ·
          refine ⟨24903032751351136280742317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16602021834234090853828211 24903032751351136280742317)
          ·
            refine ⟨9338637281756676105278369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24903032751351136280742317 9338637281756676105278369)
            ·
              refine ⟨7003977961317507078958777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9338637281756676105278369 7003977961317507078958777)
              ·
                refine ⟨5252983470988130309219083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7003977961317507078958777 5252983470988130309219083)
                ·
                  refine ⟨7879475206482195463828625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5252983470988130309219083 7879475206482195463828625)
                  ·
                    refine ⟨5909606404861646597871469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7879475206482195463828625 5909606404861646597871469)
                    ·
                      refine ⟨2216102401823117474201801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5909606404861646597871469 2216102401823117474201801)
                      ·
                        rfl

theorem cell23_4315844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_4315844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315844 prefixEnd_4315844 := by exact prefixLift 4315844
  have htrace : WordTrace (prefixWord ++ tailWord_4315844) baseStart_4315844 baseEnd_4315844 := by
    simpa [prefixWord, tailWord_4315844, baseEnd_4315844] using wordTrace_append hprefix tailTrace_4315844
  have hstable : (prefixWord ++ tailWord_4315844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315844).length < 2 ^ (prefixWord ++ tailWord_4315844).sum := by decide
  have hdescent : baseEnd_4315844 < baseStart_4315844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315883 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 5]
def baseStart_4315883 : Nat := 118140960795 + 4315883 * 2 ^ 59
def prefixEnd_4315883 : Nat := 4983230072969 + 3 ^ 40 * 4315883 * 2
def baseEnd_4315883 : Nat := 2216122427568642821614121

theorem tailTrace_4315883 : CollatzResearch.WordTrace tailWord_4315883 prefixEnd_4315883 2216122427568642821614121 := by
  unfold tailWord_4315883
  simp only [CollatzResearch.WordTrace]
  refine ⟨157413185023300459978448303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104942123348866973318965535 157413185023300459978448303)
  ·
    refine ⟨236119777534950689967672455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157413185023300459978448303 236119777534950689967672455)
    ·
      refine ⟨354179666302426034951508683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236119777534950689967672455 354179666302426034951508683)
      ·
        refine ⟨531269499453639052427263025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354179666302426034951508683 531269499453639052427263025)
        ·
          refine ⟨398452124590229289320447269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 531269499453639052427263025 398452124590229289320447269)
          ·
            refine ⟨74709773360667991747583863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 398452124590229289320447269 74709773360667991747583863)
            ·
              refine ⟨112064660041001987621375795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74709773360667991747583863 112064660041001987621375795)
              ·
                refine ⟨168096990061502981432063693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112064660041001987621375795 168096990061502981432063693)
                ·
                  refine ⟨63036371273063618037023885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168096990061502981432063693 63036371273063618037023885)
                  ·
                    refine ⟨23638639227398856763883957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 63036371273063618037023885 23638639227398856763883957)
                    ·
                      refine ⟨2216122427568642821614121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23638639227398856763883957 2216122427568642821614121)
                      ·
                        rfl

theorem cell23_4315883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 5].length) (baseStart_4315883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315883 prefixEnd_4315883 := by exact prefixLift 4315883
  have htrace : WordTrace (prefixWord ++ tailWord_4315883) baseStart_4315883 baseEnd_4315883 := by
    simpa [prefixWord, tailWord_4315883, baseEnd_4315883] using wordTrace_append hprefix tailTrace_4315883
  have hstable : (prefixWord ++ tailWord_4315883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315883).length < 2 ^ (prefixWord ++ tailWord_4315883).sum := by decide
  have hdescent : baseEnd_4315883 < baseStart_4315883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315900 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_4315900 : Nat := 118140960795 + 4315900 * 2 ^ 59
def prefixEnd_4315900 : Nat := 4983230072969 + 3 ^ 40 * 4315900 * 2
def baseEnd_4315900 : Nat := 2216131156739769255101543

theorem tailTrace_4315900 : CollatzResearch.WordTrace tailWord_4315900 prefixEnd_4315900 2216131156739769255101543 := by
  unfold tailWord_4315900
  simp only [CollatzResearch.WordTrace]
  refine ⟨78706902532119435940908577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104942536709492581254544769 78706902532119435940908577)
  ·
    refine ⟨59030176899089576955681433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78706902532119435940908577 59030176899089576955681433)
    ·
      refine ⟨44272632674317182716761075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59030176899089576955681433 44272632674317182716761075)
      ·
        refine ⟨66408949011475774075141613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44272632674317182716761075 66408949011475774075141613)
        ·
          refine ⟨24903355879303415278178105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66408949011475774075141613 24903355879303415278178105)
          ·
            refine ⟨18677516909477561458633579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24903355879303415278178105 18677516909477561458633579)
            ·
              refine ⟨28016275364216342187950369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18677516909477561458633579 28016275364216342187950369)
              ·
                refine ⟨21012206523162256640962777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28016275364216342187950369 21012206523162256640962777)
                ·
                  refine ⟨15759154892371692480722083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21012206523162256640962777 15759154892371692480722083)
                  ·
                    refine ⟨23638732338557538721083125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15759154892371692480722083 23638732338557538721083125)
                    ·
                      refine ⟨2216131156739769255101543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23638732338557538721083125 2216131156739769255101543)
                      ·
                        rfl

theorem cell23_4315900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_4315900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315900 prefixEnd_4315900 := by exact prefixLift 4315900
  have htrace : WordTrace (prefixWord ++ tailWord_4315900) baseStart_4315900 baseEnd_4315900 := by
    simpa [prefixWord, tailWord_4315900, baseEnd_4315900] using wordTrace_append hprefix tailTrace_4315900
  have hstable : (prefixWord ++ tailWord_4315900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315900).length < 2 ^ (prefixWord ++ tailWord_4315900).sum := by decide
  have hdescent : baseEnd_4315900 < baseStart_4315900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315903 : List Nat := [1, 1, 2, 2, 1, 3, 1, 3, 9]
def baseStart_4315903 : Nat := 118140960795 + 4315903 * 2 ^ 59
def prefixEnd_4315903 : Nat := 4983230072969 + 3 ^ 40 * 4315903 * 2
def baseEnd_4315903 : Nat := 246236966353525860373781

theorem tailTrace_4315903 : CollatzResearch.WordTrace tailWord_4315903 prefixEnd_4315903 246236966353525860373781 := by
  unfold tailWord_4315903
  simp only [CollatzResearch.WordTrace]
  refine ⟨157413914483228003394176363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104942609655485335596117575 157413914483228003394176363)
  ·
    refine ⟨236120871724842005091264545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157413914483228003394176363 236120871724842005091264545)
    ·
      refine ⟨177090653793631503818448409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236120871724842005091264545 177090653793631503818448409)
      ·
        refine ⟨132817990345223627863836307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177090653793631503818448409 132817990345223627863836307)
        ·
          refine ⟨199226985517835441795754461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132817990345223627863836307 199226985517835441795754461)
          ·
            refine ⟨74710119569188290673407923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 199226985517835441795754461 74710119569188290673407923)
            ·
              refine ⟨112065179353782436010111885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74710119569188290673407923 112065179353782436010111885)
              ·
                refine ⟨42024442257668413503791957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112065179353782436010111885 42024442257668413503791957)
                ·
                  refine ⟨246236966353525860373781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 42024442257668413503791957 246236966353525860373781)
                  ·
                    rfl

theorem cell23_4315903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 9].length) (baseStart_4315903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315903 prefixEnd_4315903 := by exact prefixLift 4315903
  have htrace : WordTrace (prefixWord ++ tailWord_4315903) baseStart_4315903 baseEnd_4315903 := by
    simpa [prefixWord, tailWord_4315903, baseEnd_4315903] using wordTrace_append hprefix tailTrace_4315903
  have hstable : (prefixWord ++ tailWord_4315903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315903).length < 2 ^ (prefixWord ++ tailWord_4315903).sum := by decide
  have hdescent : baseEnd_4315903 < baseStart_4315903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315937 : List Nat := [1, 2, 3, 2, 1, 2, 3, 4, 5]
def baseStart_4315937 : Nat := 118140960795 + 4315937 * 2 ^ 59
def prefixEnd_4315937 : Nat := 4983230072969 + 3 ^ 40 * 4315937 * 2
def baseEnd_4315937 : Nat := 246238906169331734482097

theorem tailTrace_4315937 : CollatzResearch.WordTrace tailWord_4315937 prefixEnd_4315937 246238906169331734482097 := by
  unfold tailWord_4315937
  simp only [CollatzResearch.WordTrace]
  refine ⟨157415154565104827200914065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104943436376736551467276043 157415154565104827200914065)
  ·
    refine ⟨118061365923828620400685549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157415154565104827200914065 118061365923828620400685549)
    ·
      refine ⟨44273012221435732650257081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118061365923828620400685549 44273012221435732650257081)
      ·
        refine ⟨33204759166076799487692811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44273012221435732650257081 33204759166076799487692811)
        ·
          refine ⟨49807138749115199231539217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33204759166076799487692811 49807138749115199231539217)
          ·
            refine ⟨37355354061836399423654413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49807138749115199231539217 37355354061836399423654413)
            ·
              refine ⟨14008257773188649783870405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37355354061836399423654413 14008257773188649783870405)
              ·
                refine ⟨2626548332472871834475701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14008257773188649783870405 2626548332472871834475701)
                ·
                  refine ⟨246238906169331734482097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2626548332472871834475701 246238906169331734482097)
                  ·
                    rfl

theorem cell23_4315937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 5].length) (baseStart_4315937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315937 prefixEnd_4315937 := by exact prefixLift 4315937
  have htrace : WordTrace (prefixWord ++ tailWord_4315937) baseStart_4315937 baseEnd_4315937 := by
    simpa [prefixWord, tailWord_4315937, baseEnd_4315937] using wordTrace_append hprefix tailTrace_4315937
  have hstable : (prefixWord ++ tailWord_4315937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315937).length < 2 ^ (prefixWord ++ tailWord_4315937).sum := by decide
  have hdescent : baseEnd_4315937 < baseStart_4315937 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4315967 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 2, 5]
def baseStart_4315967 : Nat := 118140960795 + 4315967 * 2 ^ 59
def prefixEnd_4315967 : Nat := 4983230072969 + 3 ^ 40 * 4315967 * 2
def baseEnd_4315967 : Nat := 738721853314540164321245

theorem tailTrace_4315967 : CollatzResearch.WordTrace tailWord_4315967 prefixEnd_4315967 738721853314540164321245 := by
  unfold tailWord_4315967
  simp only [CollatzResearch.WordTrace]
  refine ⟨157416248754996142324506155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104944165836664094883004103 157416248754996142324506155)
  ·
    refine ⟨236124373132494213486759233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157416248754996142324506155 236124373132494213486759233)
    ·
      refine ⟨177093279849370660115069425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236124373132494213486759233 177093279849370660115069425)
      ·
        refine ⟨132819959887027995086302069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177093279849370660115069425 132819959887027995086302069)
        ·
          refine ⟨12451871239408874539340819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132819959887027995086302069 12451871239408874539340819)
          ·
            refine ⟨18677806859113311809011229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12451871239408874539340819 18677806859113311809011229)
            ·
              refine ⟨7004177572167491928379211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18677806859113311809011229 7004177572167491928379211)
              ·
                refine ⟨10506266358251237892568817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7004177572167491928379211 10506266358251237892568817)
                ·
                  refine ⟨7879699768688428419426613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10506266358251237892568817 7879699768688428419426613)
                  ·
                    refine ⟨738721853314540164321245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7879699768688428419426613 738721853314540164321245)
                    ·
                      rfl

theorem cell23_4315967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 5].length) (baseStart_4315967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4315967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4315967 prefixEnd_4315967 := by exact prefixLift 4315967
  have htrace : WordTrace (prefixWord ++ tailWord_4315967) baseStart_4315967 baseEnd_4315967 := by
    simpa [prefixWord, tailWord_4315967, baseEnd_4315967] using wordTrace_append hprefix tailTrace_4315967
  have hstable : (prefixWord ++ tailWord_4315967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4315967).length < 2 ^ (prefixWord ++ tailWord_4315967).sum := by decide
  have hdescent : baseEnd_4315967 < baseStart_4315967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4315967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316000 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 6]
def baseStart_4316000 : Nat := 118140960795 + 4316000 * 2 ^ 59
def prefixEnd_4316000 : Nat := 4983230072969 + 3 ^ 40 * 4316000 * 2
def baseEnd_4316000 : Nat := 2216182504805218863851083

theorem tailTrace_4316000 : CollatzResearch.WordTrace tailWord_4316000 prefixEnd_4316000 2216182504805218863851083 := by
  unfold tailWord_4316000
  simp only [CollatzResearch.WordTrace]
  refine ⟨78708726181938294480228727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104944968242584392640304969 78708726181938294480228727)
  ·
    refine ⟨118063089272907441720343091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78708726181938294480228727 118063089272907441720343091)
    ·
      refine ⟨177094633909361162580514637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118063089272907441720343091 177094633909361162580514637)
      ·
        refine ⟨66410487716010435967692989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177094633909361162580514637 66410487716010435967692989)
        ·
          refine ⟨24903932893503913487884871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66410487716010435967692989 24903932893503913487884871)
          ·
            refine ⟨37355899340255870231827307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24903932893503913487884871 37355899340255870231827307)
            ·
              refine ⟨56033849010383805347740961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37355899340255870231827307 56033849010383805347740961)
              ·
                refine ⟨42025386757787854010805721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56033849010383805347740961 42025386757787854010805721)
                ·
                  refine ⟨31519040068340890508104291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42025386757787854010805721 31519040068340890508104291)
                  ·
                    refine ⟨47278560102511335762156437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 31519040068340890508104291 47278560102511335762156437)
                    ·
                      refine ⟨2216182504805218863851083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47278560102511335762156437 2216182504805218863851083)
                      ·
                        rfl

theorem cell23_4316000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_4316000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316000 prefixEnd_4316000 := by exact prefixLift 4316000
  have htrace : WordTrace (prefixWord ++ tailWord_4316000) baseStart_4316000 baseEnd_4316000 := by
    simpa [prefixWord, tailWord_4316000, baseEnd_4316000] using wordTrace_append hprefix tailTrace_4316000
  have hstable : (prefixWord ++ tailWord_4316000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316000).length < 2 ^ (prefixWord ++ tailWord_4316000).sum := by decide
  have hdescent : baseEnd_4316000 < baseStart_4316000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316004 : List Nat := [2, 3, 1, 1, 4, 1, 2, 1, 2, 4, 2]
def baseStart_4316004 : Nat := 118140960795 + 4316004 * 2 ^ 59
def prefixEnd_4316004 : Nat := 4983230072969 + 3 ^ 40 * 4316004 * 2
def baseEnd_4316004 : Nat := 2216184558727836848201065

theorem tailTrace_4316004 : CollatzResearch.WordTrace tailWord_4316004 prefixEnd_4316004 2216184558727836848201065 := by
  unfold tailWord_4316004
  simp only [CollatzResearch.WordTrace]
  refine ⟨78708799127931048821801533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104945065503908065095735377 78708799127931048821801533)
  ·
    refine ⟨29515799672974143308175575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 78708799127931048821801533 29515799672974143308175575)
    ·
      refine ⟨44273699509461214962263363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29515799672974143308175575 44273699509461214962263363)
      ·
        refine ⟨66410549264191822443395045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44273699509461214962263363 66410549264191822443395045)
        ·
          refine ⟨12451977987035966708136571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66410549264191822443395045 12451977987035966708136571)
          ·
            refine ⟨18677966980553950062204857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12451977987035966708136571 18677966980553950062204857)
            ·
              refine ⟨14008475235415462546653643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18677966980553950062204857 14008475235415462546653643)
              ·
                refine ⟨21012712853123193819980465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14008475235415462546653643 21012712853123193819980465)
                ·
                  refine ⟨15759534639842395364985349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21012712853123193819980465 15759534639842395364985349)
                  ·
                    refine ⟨2954912744970449130934753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15759534639842395364985349 2954912744970449130934753)
                    ·
                      refine ⟨2216184558727836848201065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2954912744970449130934753 2216184558727836848201065)
                      ·
                        rfl

theorem cell23_4316004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 1, 2, 4, 2].length) (baseStart_4316004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316004 prefixEnd_4316004 := by exact prefixLift 4316004
  have htrace : WordTrace (prefixWord ++ tailWord_4316004) baseStart_4316004 baseEnd_4316004 := by
    simpa [prefixWord, tailWord_4316004, baseEnd_4316004] using wordTrace_append hprefix tailTrace_4316004
  have hstable : (prefixWord ++ tailWord_4316004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316004).length < 2 ^ (prefixWord ++ tailWord_4316004).sum := by decide
  have hdescent : baseEnd_4316004 < baseStart_4316004 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316007 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 3]
def baseStart_4316007 : Nat := 118140960795 + 4316007 * 2 ^ 59
def prefixEnd_4316007 : Nat := 4983230072969 + 3 ^ 40 * 4316007 * 2
def baseEnd_4316007 : Nat := 2216186099169800336463551

theorem tailTrace_4316007 : CollatzResearch.WordTrace tailWord_4316007 prefixEnd_4316007 2216186099169800336463551 := by
  unfold tailWord_4316007
  simp only [CollatzResearch.WordTrace]
  refine ⟨157417707674851229155962275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104945138449900819437308183 157417707674851229155962275)
  ·
    refine ⟨236126561512276843733943413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157417707674851229155962275 236126561512276843733943413)
    ·
      refine ⟨22136865141775954100057195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 236126561512276843733943413 22136865141775954100057195)
      ·
        refine ⟨33205297712663931150085793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22136865141775954100057195 33205297712663931150085793)
        ·
          refine ⟨24903973284497948362564345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33205297712663931150085793 24903973284497948362564345)
          ·
            refine ⟨18677979963373461271923259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24903973284497948362564345 18677979963373461271923259)
            ·
              refine ⟨28016969945060191907884889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18677979963373461271923259 28016969945060191907884889)
              ·
                refine ⟨21012727458795143930913667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28016969945060191907884889 21012727458795143930913667)
                ·
                  refine ⟨31519091188192715896370501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21012727458795143930913667 31519091188192715896370501)
                  ·
                    refine ⟨5909829597786134230569469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31519091188192715896370501 5909829597786134230569469)
                    ·
                      refine ⟨2216186099169800336463551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5909829597786134230569469 2216186099169800336463551)
                      ·
                        rfl

theorem cell23_4316007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_4316007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316007 prefixEnd_4316007 := by exact prefixLift 4316007
  have htrace : WordTrace (prefixWord ++ tailWord_4316007) baseStart_4316007 baseEnd_4316007 := by
    simpa [prefixWord, tailWord_4316007, baseEnd_4316007] using wordTrace_append hprefix tailTrace_4316007
  have hstable : (prefixWord ++ tailWord_4316007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316007).length < 2 ^ (prefixWord ++ tailWord_4316007).sum := by decide
  have hdescent : baseEnd_4316007 < baseStart_4316007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316080 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 5]
def baseStart_4316080 : Nat := 118140960795 + 4316080 * 2 ^ 59
def prefixEnd_4316080 : Nat := 4983230072969 + 3 ^ 40 * 4316080 * 2
def baseEnd_4316080 : Nat := 2216223583257578550850715

theorem tailTrace_4316080 : CollatzResearch.WordTrace tailWord_4316080 prefixEnd_4316080 2216223583257578550850715 := by
  unfold tailWord_4316080
  simp only [CollatzResearch.WordTrace]
  refine ⟨78710185101793381311684847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104946913469057841748913129 78710185101793381311684847)
  ·
    refine ⟨118065277652690071967527271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78710185101793381311684847 118065277652690071967527271)
    ·
      refine ⟨177097916479035107951290907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118065277652690071967527271 177097916479035107951290907)
      ·
        refine ⟨265646874718552661926936361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177097916479035107951290907 265646874718552661926936361)
        ·
          refine ⟨199235156038914496445202271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265646874718552661926936361 199235156038914496445202271)
          ·
            refine ⟨298852734058371744667803407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199235156038914496445202271 298852734058371744667803407)
            ·
              refine ⟨448279101087557617001705111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298852734058371744667803407 448279101087557617001705111)
              ·
                refine ⟨672418651631336425502557667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448279101087557617001705111 672418651631336425502557667)
                ·
                  refine ⟨1008627977447004638253836501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 672418651631336425502557667 1008627977447004638253836501)
                  ·
                    refine ⟨23639718221414171209074293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1008627977447004638253836501 23639718221414171209074293)
                    ·
                      refine ⟨2216223583257578550850715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23639718221414171209074293 2216223583257578550850715)
                      ·
                        rfl

theorem cell23_4316080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_4316080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316080 prefixEnd_4316080 := by exact prefixLift 4316080
  have htrace : WordTrace (prefixWord ++ tailWord_4316080) baseStart_4316080 baseEnd_4316080 := by
    simpa [prefixWord, tailWord_4316080, baseEnd_4316080] using wordTrace_append hprefix tailTrace_4316080
  have hstable : (prefixWord ++ tailWord_4316080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316080).length < 2 ^ (prefixWord ++ tailWord_4316080).sum := by decide
  have hdescent : baseEnd_4316080 < baseStart_4316080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316087 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 6, 4]
def baseStart_4316087 : Nat := 118140960795 + 4316087 * 2 ^ 59
def prefixEnd_4316087 : Nat := 4983230072969 + 3 ^ 40 * 4316087 * 2
def baseEnd_4316087 : Nat := 738742392540720007821061

theorem tailTrace_4316087 : CollatzResearch.WordTrace tailWord_4316087 prefixEnd_4316087 738742392540720007821061 := by
  unfold tailWord_4316087
  simp only [CollatzResearch.WordTrace]
  refine ⟨157420625514561402818874515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104947083676374268545916343 157420625514561402818874515)
  ·
    refine ⟨236130938271842104228311773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157420625514561402818874515 236130938271842104228311773)
    ·
      refine ⟨88549101851940789085616915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236130938271842104228311773 88549101851940789085616915)
      ·
        refine ⟨132823652777911183628425373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88549101851940789085616915 132823652777911183628425373)
        ·
          refine ⟨49808869791716693860659515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132823652777911183628425373 49808869791716693860659515)
          ·
            refine ⟨74713304687575040790989273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49808869791716693860659515 74713304687575040790989273)
            ·
              refine ⟨56034978515681280593241955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74713304687575040790989273 56034978515681280593241955)
              ·
                refine ⟨84052467773521920889862933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56034978515681280593241955 84052467773521920889862933)
                ·
                  refine ⟨3939959426883840041712325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 84052467773521920889862933 3939959426883840041712325)
                  ·
                    refine ⟨738742392540720007821061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3939959426883840041712325 738742392540720007821061)
                    ·
                      rfl

theorem cell23_4316087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_4316087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316087 prefixEnd_4316087 := by exact prefixLift 4316087
  have htrace : WordTrace (prefixWord ++ tailWord_4316087) baseStart_4316087 baseEnd_4316087 := by
    simpa [prefixWord, tailWord_4316087, baseEnd_4316087] using wordTrace_append hprefix tailTrace_4316087
  have hstable : (prefixWord ++ tailWord_4316087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316087).length < 2 ^ (prefixWord ++ tailWord_4316087).sum := by decide
  have hdescent : baseEnd_4316087 < baseStart_4316087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316144 : List Nat := [2, 1, 1, 1, 3, 2, 1, 4, 4, 1, 3]
def baseStart_4316144 : Nat := 118140960795 + 4316144 * 2 ^ 59
def prefixEnd_4316144 : Nat := 4983230072969 + 3 ^ 40 * 4316144 * 2
def baseEnd_4316144 : Nat := 2216256446019466300450421

theorem tailTrace_4316144 : CollatzResearch.WordTrace tailWord_4316144 prefixEnd_4316144 2216256446019466300450421 := by
  unfold tailWord_4316144
  simp only [CollatzResearch.WordTrace]
  refine ⟨78711352237677450776849743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104948469650236601035799657 78711352237677450776849743)
  ·
    refine ⟨118067028356516176165274615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78711352237677450776849743 118067028356516176165274615)
    ·
      refine ⟨177100542534774264247911923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118067028356516176165274615 177100542534774264247911923)
      ·
        refine ⟨265650813802161396371867885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177100542534774264247911923 265650813802161396371867885)
        ·
          refine ⟨99619055175810523639450457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 265650813802161396371867885 99619055175810523639450457)
          ·
            refine ⟨74714291381857892729587843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99619055175810523639450457 74714291381857892729587843)
            ·
              refine ⟨112071437072786839094381765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74714291381857892729587843 112071437072786839094381765)
              ·
                refine ⟨21013394451147532330196581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112071437072786839094381765 21013394451147532330196581)
                ·
                  refine ⟨3940011459590162311911859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21013394451147532330196581 3940011459590162311911859)
                  ·
                    refine ⟨5910017189385243467867789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3940011459590162311911859 5910017189385243467867789)
                    ·
                      refine ⟨2216256446019466300450421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5910017189385243467867789 2216256446019466300450421)
                      ·
                        rfl

theorem cell23_4316144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 4, 4, 1, 3].length) (baseStart_4316144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316144 prefixEnd_4316144 := by exact prefixLift 4316144
  have htrace : WordTrace (prefixWord ++ tailWord_4316144) baseStart_4316144 baseEnd_4316144 := by
    simpa [prefixWord, tailWord_4316144, baseEnd_4316144] using wordTrace_append hprefix tailTrace_4316144
  have hstable : (prefixWord ++ tailWord_4316144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316144).length < 2 ^ (prefixWord ++ tailWord_4316144).sum := by decide
  have hdescent : baseEnd_4316144 < baseStart_4316144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316145 : List Nat := [1, 2, 2, 2, 4, 2, 2, 3, 1, 2, 2]
def baseStart_4316145 : Nat := 118140960795 + 4316145 * 2 ^ 59
def prefixEnd_4316145 : Nat := 4983230072969 + 3 ^ 40 * 4316145 * 2
def baseEnd_4316145 : Nat := 2216256959500120796537917

theorem tailTrace_4316145 : CollatzResearch.WordTrace tailWord_4316145 prefixEnd_4316145 2216256959500120796537917 := by
  unfold tailWord_4316145
  simp only [CollatzResearch.WordTrace]
  refine ⟨157422740948351278724485889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104948493965567519149657259 157422740948351278724485889)
  ·
    refine ⟨118067055711263459043364417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157422740948351278724485889 118067055711263459043364417)
    ·
      refine ⟨88550291783447594282523313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118067055711263459043364417 88550291783447594282523313)
      ·
        refine ⟨66412718837585695711892485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88550291783447594282523313 66412718837585695711892485)
        ·
          refine ⟨12452384782047317945979841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66412718837585695711892485 12452384782047317945979841)
          ·
            refine ⟨9339288586535488459484881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12452384782047317945979841 9339288586535488459484881)
            ·
              refine ⟨7004466439901616344613661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9339288586535488459484881 7004466439901616344613661)
              ·
                refine ⟨2626674914963106129230123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7004466439901616344613661 2626674914963106129230123)
                ·
                  refine ⟨3940012372444659193845185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2626674914963106129230123 3940012372444659193845185)
                  ·
                    refine ⟨2955009279333494395383889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3940012372444659193845185 2955009279333494395383889)
                    ·
                      refine ⟨2216256959500120796537917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2955009279333494395383889 2216256959500120796537917)
                      ·
                        rfl

theorem cell23_4316145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_4316145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316145 prefixEnd_4316145 := by exact prefixLift 4316145
  have htrace : WordTrace (prefixWord ++ tailWord_4316145) baseStart_4316145 baseEnd_4316145 := by
    simpa [prefixWord, tailWord_4316145, baseEnd_4316145] using wordTrace_append hprefix tailTrace_4316145
  have hstable : (prefixWord ++ tailWord_4316145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316145).length < 2 ^ (prefixWord ++ tailWord_4316145).sum := by decide
  have hdescent : baseEnd_4316145 < baseStart_4316145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316161 : List Nat := [1, 2, 4, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_4316161 : Nat := 118140960795 + 4316161 * 2 ^ 59
def prefixEnd_4316161 : Nat := 4983230072969 + 3 ^ 40 * 4316161 * 2
def baseEnd_4316161 : Nat := 2216265175190592733937843

theorem tailTrace_4316161 : CollatzResearch.WordTrace tailWord_4316161 prefixEnd_4316161 2216265175190592733937843 := by
  unfold tailWord_4316161
  simp only [CollatzResearch.WordTrace]
  refine ⟨157423324516293313457068337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104948883010862208971378891 157423324516293313457068337)
  ·
    refine ⟨118067493387219985092801253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157423324516293313457068337 118067493387219985092801253)
    ·
      refine ⟨22137655010103747204900235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118067493387219985092801253 22137655010103747204900235)
      ·
        refine ⟨33206482515155620807350353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22137655010103747204900235 33206482515155620807350353)
        ·
          refine ⟨24904861886366715605512765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33206482515155620807350353 24904861886366715605512765)
          ·
            refine ⟨9339323207387518352067287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24904861886366715605512765 9339323207387518352067287)
            ·
              refine ⟨14008984811081277528100931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9339323207387518352067287 14008984811081277528100931)
              ·
                refine ⟨21013477216621916292151397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14008984811081277528100931 21013477216621916292151397)
                ·
                  refine ⟨3940026978116609304778387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21013477216621916292151397 3940026978116609304778387)
                  ·
                    refine ⟨5910040467174913957167581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3940026978116609304778387 5910040467174913957167581)
                    ·
                      refine ⟨2216265175190592733937843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5910040467174913957167581 2216265175190592733937843)
                      ·
                        rfl

theorem cell23_4316161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_4316161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316161 prefixEnd_4316161 := by exact prefixLift 4316161
  have htrace : WordTrace (prefixWord ++ tailWord_4316161) baseStart_4316161 baseEnd_4316161 := by
    simpa [prefixWord, tailWord_4316161, baseEnd_4316161] using wordTrace_append hprefix tailTrace_4316161
  have hstable : (prefixWord ++ tailWord_4316161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316161).length < 2 ^ (prefixWord ++ tailWord_4316161).sum := by decide
  have hdescent : baseEnd_4316161 < baseStart_4316161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316162 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_4316162 : Nat := 118140960795 + 4316162 * 2 ^ 59
def prefixEnd_4316162 : Nat := 4983230072969 + 3 ^ 40 * 4316162 * 2
def baseEnd_4316162 : Nat := 2216265688671247230025339

theorem tailTrace_4316162 : CollatzResearch.WordTrace tailWord_4316162 prefixEnd_4316162 2216265688671247230025339 := by
  unfold tailWord_4316162
  simp only [CollatzResearch.WordTrace]
  refine ⟨39355840247322422656963685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104948907326193127085236493 39355840247322422656963685)
  ·
    refine ⟨7379220046372954248180691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 39355840247322422656963685 7379220046372954248180691)
    ·
      refine ⟨11068830069559431372271037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7379220046372954248180691 11068830069559431372271037)
      ·
        refine ⟨4150811276084786764601639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11068830069559431372271037 4150811276084786764601639)
        ·
          refine ⟨6226216914127180146902459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4150811276084786764601639 6226216914127180146902459)
          ·
            refine ⟨9339325371190770220353689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6226216914127180146902459 9339325371190770220353689)
            ·
              refine ⟨7004494028393077665265267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9339325371190770220353689 7004494028393077665265267)
              ·
                refine ⟨10506741042589616497897901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7004494028393077665265267 10506741042589616497897901)
                ·
                  refine ⟨3940027890971106186711713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10506741042589616497897901 3940027890971106186711713)
                  ·
                    refine ⟨2955020918228329640033785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3940027890971106186711713 2955020918228329640033785)
                    ·
                      refine ⟨2216265688671247230025339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2955020918228329640033785 2216265688671247230025339)
                      ·
                        rfl

theorem cell23_4316162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_4316162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316162 prefixEnd_4316162 := by exact prefixLift 4316162
  have htrace : WordTrace (prefixWord ++ tailWord_4316162) baseStart_4316162 baseEnd_4316162 := by
    simpa [prefixWord, tailWord_4316162, baseEnd_4316162] using wordTrace_append hprefix tailTrace_4316162
  have hstable : (prefixWord ++ tailWord_4316162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316162).length < 2 ^ (prefixWord ++ tailWord_4316162).sum := by decide
  have hdescent : baseEnd_4316162 < baseStart_4316162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316187 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 3]
def baseStart_4316187 : Nat := 118140960795 + 4316187 * 2 ^ 59
def prefixEnd_4316187 : Nat := 4983230072969 + 3 ^ 40 * 4316187 * 2
def baseEnd_4316187 : Nat := 2216278525687609632212723

theorem tailTrace_4316187 : CollatzResearch.WordTrace tailWord_4316187 prefixEnd_4316187 2216278525687609632212723 := by
  unfold tailWord_4316187
  simp only [CollatzResearch.WordTrace]
  refine ⟨157424272814199119897514815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104949515209466079931676543 157424272814199119897514815)
  ·
    refine ⟨236136409221298679846272223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157424272814199119897514815 236136409221298679846272223)
    ·
      refine ⟨354204613831948019769408335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236136409221298679846272223 354204613831948019769408335)
      ·
        refine ⟨531306920747922029654112503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354204613831948019769408335 531306920747922029654112503)
        ·
          refine ⟨796960381121883044481168755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531306920747922029654112503 796960381121883044481168755)
          ·
            refine ⟨1195440571682824566721753133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796960381121883044481168755 1195440571682824566721753133)
            ·
              refine ⟨448290214381059212520657425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1195440571682824566721753133 448290214381059212520657425)
              ·
                refine ⟨336217660785794409390493069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448290214381059212520657425 336217660785794409390493069)
                ·
                  refine ⟨126081622794672903521434901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336217660785794409390493069 126081622794672903521434901)
                  ·
                    refine ⟨5910076068500292352567261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 126081622794672903521434901 5910076068500292352567261)
                    ·
                      refine ⟨2216278525687609632212723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5910076068500292352567261 2216278525687609632212723)
                      ·
                        rfl

theorem cell23_4316187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 3].length) (baseStart_4316187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316187 prefixEnd_4316187 := by exact prefixLift 4316187
  have htrace : WordTrace (prefixWord ++ tailWord_4316187) baseStart_4316187 baseEnd_4316187 := by
    simpa [prefixWord, tailWord_4316187, baseEnd_4316187] using wordTrace_append hprefix tailTrace_4316187
  have hstable : (prefixWord ++ tailWord_4316187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316187).length < 2 ^ (prefixWord ++ tailWord_4316187).sum := by decide
  have hdescent : baseEnd_4316187 < baseStart_4316187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316234 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 2, 3, 3]
def baseStart_4316234 : Nat := 118140960795 + 4316234 * 2 ^ 59
def prefixEnd_4316234 : Nat := 4983230072969 + 3 ^ 40 * 4316234 * 2
def baseEnd_4316234 : Nat := 2216302659278370948325007

theorem tailTrace_4316234 : CollatzResearch.WordTrace tailWord_4316234 prefixEnd_4316234 2216302659278370948325007 := by
  unfold tailWord_4316234
  simp only [CollatzResearch.WordTrace]
  refine ⟨39356496761257211731118939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104950658030019231282983837 39356496761257211731118939)
  ·
    refine ⟨59034745141885817596678409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39356496761257211731118939 59034745141885817596678409)
    ·
      refine ⟨44276058856414363197508807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59034745141885817596678409 44276058856414363197508807)
      ·
        refine ⟨66414088284621544796263211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44276058856414363197508807 66414088284621544796263211)
        ·
          refine ⟨99621132426932317194394817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66414088284621544796263211 99621132426932317194394817)
          ·
            refine ⟨74715849320199237895796113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99621132426932317194394817 74715849320199237895796113)
            ·
              refine ⟨56036886990149428421847085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74715849320199237895796113 56036886990149428421847085)
              ·
                refine ⟨21013832621306035658192657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56036886990149428421847085 21013832621306035658192657)
                ·
                  refine ⟨15760374465979526743644493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21013832621306035658192657 15760374465979526743644493)
                  ·
                    refine ⟨5910140424742322528866685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15760374465979526743644493 5910140424742322528866685)
                    ·
                      refine ⟨2216302659278370948325007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5910140424742322528866685 2216302659278370948325007)
                      ·
                        rfl

theorem cell23_4316234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_4316234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316234 prefixEnd_4316234 := by exact prefixLift 4316234
  have htrace : WordTrace (prefixWord ++ tailWord_4316234) baseStart_4316234 baseEnd_4316234 := by
    simpa [prefixWord, tailWord_4316234, baseEnd_4316234] using wordTrace_append hprefix tailTrace_4316234
  have hstable : (prefixWord ++ tailWord_4316234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316234).length < 2 ^ (prefixWord ++ tailWord_4316234).sum := by decide
  have hdescent : baseEnd_4316234 < baseStart_4316234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316247 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 7]
def baseStart_4316247 : Nat := 118140960795 + 4316247 * 2 ^ 59
def prefixEnd_4316247 : Nat := 4983230072969 + 3 ^ 40 * 4316247 * 2
def baseEnd_4316247 : Nat := 2216309334526879397462447

theorem tailTrace_4316247 : CollatzResearch.WordTrace tailWord_4316247 prefixEnd_4316247 2216309334526879397462447 := by
  unfold tailWord_4316247
  simp only [CollatzResearch.WordTrace]
  refine ⟨157426461193981750144698995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104950974129321166763132663 157426461193981750144698995)
  ·
    refine ⟨236139691790972625217048493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157426461193981750144698995 236139691790972625217048493)
    ·
      refine ⟨88552384421614734456393185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236139691790972625217048493 88552384421614734456393185)
      ·
        refine ⟨66414288316211050842294889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88552384421614734456393185 66414288316211050842294889)
        ·
          refine ⟨49810716237158288131721167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66414288316211050842294889 49810716237158288131721167)
          ·
            refine ⟨74716074355737432197581751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49810716237158288131721167 74716074355737432197581751)
            ·
              refine ⟨112074111533606148296372627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74716074355737432197581751 112074111533606148296372627)
              ·
                refine ⟨168111167300409222444558941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112074111533606148296372627 168111167300409222444558941)
                ·
                  refine ⟨63041687737653458416709603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 168111167300409222444558941 63041687737653458416709603)
                  ·
                    refine ⟨94562531606480187625064405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 63041687737653458416709603 94562531606480187625064405)
                    ·
                      refine ⟨2216309334526879397462447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 94562531606480187625064405 2216309334526879397462447)
                      ·
                        rfl

theorem cell23_4316247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_4316247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316247 prefixEnd_4316247 := by exact prefixLift 4316247
  have htrace : WordTrace (prefixWord ++ tailWord_4316247) baseStart_4316247 baseEnd_4316247 := by
    simpa [prefixWord, tailWord_4316247, baseEnd_4316247] using wordTrace_append hprefix tailTrace_4316247
  have hstable : (prefixWord ++ tailWord_4316247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316247).length < 2 ^ (prefixWord ++ tailWord_4316247).sum := by decide
  have hdescent : baseEnd_4316247 < baseStart_4316247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316291 : List Nat := [1, 1, 1, 3, 3, 2, 3, 1, 2, 4, 2]
def baseStart_4316291 : Nat := 118140960795 + 4316291 * 2 ^ 59
def prefixEnd_4316291 : Nat := 4983230072969 + 3 ^ 40 * 4316291 * 2
def baseEnd_4316291 : Nat := 2216331927675677225312245

theorem tailTrace_4316291 : CollatzResearch.WordTrace tailWord_4316291 prefixEnd_4316291 2216331927675677225312245 := by
  unfold tailWord_4316291
  simp only [CollatzResearch.WordTrace]
  refine ⟨157428066005822345659300727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104952044003881563772867151 157428066005822345659300727)
  ·
    refine ⟨236142099008733518488951091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157428066005822345659300727 236142099008733518488951091)
    ·
      refine ⟨354213148513100277733426637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236142099008733518488951091 354213148513100277733426637)
      ·
        refine ⟨132829930692412604150034989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 354213148513100277733426637 132829930692412604150034989)
        ·
          refine ⟨49811224009654726556263121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 132829930692412604150034989 49811224009654726556263121)
          ·
            refine ⟨37358418007241044917197341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49811224009654726556263121 37358418007241044917197341)
            ·
              refine ⟨14009406752715391843949003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37358418007241044917197341 14009406752715391843949003)
              ·
                refine ⟨21014110129073087765923505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14009406752715391843949003 21014110129073087765923505)
                ·
                  refine ⟨15760582596804815824442629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21014110129073087765923505 15760582596804815824442629)
                  ·
                    refine ⟨2955109236900902967082993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15760582596804815824442629 2955109236900902967082993)
                    ·
                      refine ⟨2216331927675677225312245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2955109236900902967082993 2216331927675677225312245)
                      ·
                        rfl

theorem cell23_4316291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 4, 2].length) (baseStart_4316291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316291 prefixEnd_4316291 := by exact prefixLift 4316291
  have htrace : WordTrace (prefixWord ++ tailWord_4316291) baseStart_4316291 baseEnd_4316291 := by
    simpa [prefixWord, tailWord_4316291, baseEnd_4316291] using wordTrace_append hprefix tailTrace_4316291
  have hstable : (prefixWord ++ tailWord_4316291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316291).length < 2 ^ (prefixWord ++ tailWord_4316291).sum := by decide
  have hdescent : baseEnd_4316291 < baseStart_4316291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316311 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 3]
def baseStart_4316311 : Nat := 118140960795 + 4316311 * 2 ^ 59
def prefixEnd_4316311 : Nat := 4983230072969 + 3 ^ 40 * 4316311 * 2
def baseEnd_4316311 : Nat := 2216342197288767147062153

theorem tailTrace_4316311 : CollatzResearch.WordTrace tailWord_4316311 prefixEnd_4316311 2216342197288767147062153 := by
  unfold tailWord_4316311
  simp only [CollatzResearch.WordTrace]
  refine ⟨157428795465749889075028787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104952530310499926050019191 157428795465749889075028787)
  ·
    refine ⟨236143193198624833612543181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157428795465749889075028787 236143193198624833612543181)
    ·
      refine ⟨88553697449484312604703693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236143193198624833612543181 88553697449484312604703693)
      ·
        refine ⟨33207636543556617226763885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88553697449484312604703693 33207636543556617226763885)
        ·
          refine ⟨12452863703833731460036457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33207636543556617226763885 12452863703833731460036457)
          ·
            refine ⟨9339647777875298595027343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12452863703833731460036457 9339647777875298595027343)
            ·
              refine ⟨14009471666812947892541015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9339647777875298595027343 14009471666812947892541015)
              ·
                refine ⟨21014207500219421838811523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14009471666812947892541015 21014207500219421838811523)
                ·
                  refine ⟨31521311250329132758217285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21014207500219421838811523 31521311250329132758217285)
                  ·
                    refine ⟨5910245859436712392165741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31521311250329132758217285 5910245859436712392165741)
                    ·
                      refine ⟨2216342197288767147062153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5910245859436712392165741 2216342197288767147062153)
                      ·
                        rfl

theorem cell23_4316311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_4316311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316311 prefixEnd_4316311 := by exact prefixLift 4316311
  have htrace : WordTrace (prefixWord ++ tailWord_4316311) baseStart_4316311 baseEnd_4316311 := by
    simpa [prefixWord, tailWord_4316311, baseEnd_4316311] using wordTrace_append hprefix tailTrace_4316311
  have hstable : (prefixWord ++ tailWord_4316311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316311).length < 2 ^ (prefixWord ++ tailWord_4316311).sum := by decide
  have hdescent : baseEnd_4316311 < baseStart_4316311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316344 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 3, 5]
def baseStart_4316344 : Nat := 118140960795 + 4316344 * 2 ^ 59
def prefixEnd_4316344 : Nat := 4983230072969 + 3 ^ 40 * 4316344 * 2
def baseEnd_4316344 : Nat := 738786380716788505983167

theorem tailTrace_4316344 : CollatzResearch.WordTrace tailWord_4316344 prefixEnd_4316344 738786380716788505983167 := by
  unfold tailWord_4316344
  simp only [CollatzResearch.WordTrace]
  refine ⟨78714999537315167855490043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104953332716420223807320057 78714999537315167855490043)
  ·
    refine ⟨118072499305972751783235065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78714999537315167855490043 118072499305972751783235065)
    ·
      refine ⟨88554374479479563837426299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118072499305972751783235065 88554374479479563837426299)
      ·
        refine ⟨132831561719219345756139449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88554374479479563837426299 132831561719219345756139449)
        ·
          refine ⟨99623671289414509317104587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132831561719219345756139449 99623671289414509317104587)
          ·
            refine ⟨149435506934121763975656881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99623671289414509317104587 149435506934121763975656881)
            ·
              refine ⟨112076630200591322981742661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149435506934121763975656881 112076630200591322981742661)
              ·
                refine ⟨21014368162610873059076749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112076630200591322981742661 21014368162610873059076749)
                ·
                  refine ⟨7880388060979077397153781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21014368162610873059076749 7880388060979077397153781)
                  ·
                    refine ⟨738786380716788505983167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7880388060979077397153781 738786380716788505983167)
                    ·
                      rfl

theorem cell23_4316344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_4316344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316344 prefixEnd_4316344 := by exact prefixLift 4316344
  have htrace : WordTrace (prefixWord ++ tailWord_4316344) baseStart_4316344 baseEnd_4316344 := by
    simpa [prefixWord, tailWord_4316344, baseEnd_4316344] using wordTrace_append hprefix tailTrace_4316344
  have hstable : (prefixWord ++ tailWord_4316344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316344).length < 2 ^ (prefixWord ++ tailWord_4316344).sum := by decide
  have hdescent : baseEnd_4316344 < baseStart_4316344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316348 : List Nat := [2, 2, 2, 3, 2, 2, 3, 1, 6]
def baseStart_4316348 : Nat := 118140960795 + 4316348 * 2 ^ 59
def prefixEnd_4316348 : Nat := 4983230072969 + 3 ^ 40 * 4316348 * 2
def baseEnd_4316348 : Nat := 246262355119220389144387

theorem tailTrace_4316348 : CollatzResearch.WordTrace tailWord_4316348 prefixEnd_4316348 246262355119220389144387 := by
  unfold tailWord_4316348
  simp only [CollatzResearch.WordTrace]
  refine ⟨78715072483307922197062849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104953429977743896262750465 78715072483307922197062849)
  ·
    refine ⟨59036304362480941647797137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78715072483307922197062849 59036304362480941647797137)
    ·
      refine ⟨44277228271860706235847853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59036304362480941647797137 44277228271860706235847853)
      ·
        refine ⟨16603960601947764838442945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44277228271860706235847853 16603960601947764838442945)
        ·
          refine ⟨12452970451460823628832209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16603960601947764838442945 12452970451460823628832209)
          ·
            refine ⟨9339727838595617721624157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12452970451460823628832209 9339727838595617721624157)
            ·
              refine ⟨3502397939473356645609059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9339727838595617721624157 3502397939473356645609059)
              ·
                refine ⟨5253596909210034968413589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3502397939473356645609059 5253596909210034968413589)
                ·
                  refine ⟨246262355119220389144387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5253596909210034968413589 246262355119220389144387)
                  ·
                    rfl

theorem cell23_4316348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 6].length) (baseStart_4316348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316348 prefixEnd_4316348 := by exact prefixLift 4316348
  have htrace : WordTrace (prefixWord ++ tailWord_4316348) baseStart_4316348 baseEnd_4316348 := by
    simpa [prefixWord, tailWord_4316348, baseEnd_4316348] using wordTrace_append hprefix tailTrace_4316348
  have hstable : (prefixWord ++ tailWord_4316348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316348).length < 2 ^ (prefixWord ++ tailWord_4316348).sum := by decide
  have hdescent : baseEnd_4316348 < baseStart_4316348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316351 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 1, 5, 2]
def baseStart_4316351 : Nat := 118140960795 + 4316351 * 2 ^ 59
def prefixEnd_4316351 : Nat := 4983230072969 + 3 ^ 40 * 4316351 * 2
def baseEnd_4316351 : Nat := 2216362736514946990561969

theorem tailTrace_4316351 : CollatzResearch.WordTrace tailWord_4316351 prefixEnd_4316351 2216362736514946990561969 := by
  unfold tailWord_4316351
  simp only [CollatzResearch.WordTrace]
  refine ⟨157430254385604975906484907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104953502923736650604323271 157430254385604975906484907)
  ·
    refine ⟨236145381578407463859727361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157430254385604975906484907 236145381578407463859727361)
    ·
      refine ⟨177109036183805597894795521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236145381578407463859727361 177109036183805597894795521)
      ·
        refine ⟨132831777137854198421096641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177109036183805597894795521 132831777137854198421096641)
        ·
          refine ⟨99623832853390648815822481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132831777137854198421096641 99623832853390648815822481)
          ·
            refine ⟨74717874640042986611866861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99623832853390648815822481 74717874640042986611866861)
            ·
              refine ⟨28019202990016119979450073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 74717874640042986611866861 28019202990016119979450073)
              ·
                refine ⟨21014402242512089984587555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28019202990016119979450073 21014402242512089984587555)
                ·
                  refine ⟨31521603363768134976881333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21014402242512089984587555 31521603363768134976881333)
                  ·
                    refine ⟨2955150315353262654082625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 31521603363768134976881333 2955150315353262654082625)
                    ·
                      refine ⟨2216362736514946990561969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2955150315353262654082625 2216362736514946990561969)
                      ·
                        rfl

theorem cell23_4316351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 5, 2].length) (baseStart_4316351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316351 prefixEnd_4316351 := by exact prefixLift 4316351
  have htrace : WordTrace (prefixWord ++ tailWord_4316351) baseStart_4316351 baseEnd_4316351 := by
    simpa [prefixWord, tailWord_4316351, baseEnd_4316351] using wordTrace_append hprefix tailTrace_4316351
  have hstable : (prefixWord ++ tailWord_4316351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316351).length < 2 ^ (prefixWord ++ tailWord_4316351).sum := by decide
  have hdescent : baseEnd_4316351 < baseStart_4316351 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316375 : List Nat := [1, 1, 3, 2, 1, 2, 5, 3, 1, 1, 3]
def baseStart_4316375 : Nat := 118140960795 + 4316375 * 2 ^ 59
def prefixEnd_4316375 : Nat := 4983230072969 + 3 ^ 40 * 4316375 * 2
def baseEnd_4316375 : Nat := 2216375060050654896661859

theorem tailTrace_4316375 : CollatzResearch.WordTrace tailWord_4316375 prefixEnd_4316375 2216375060050654896661859 := by
  unfold tailWord_4316375
  simp only [CollatzResearch.WordTrace]
  refine ⟨157431129737518028005358579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104954086491678685336905719 157431129737518028005358579)
  ·
    refine ⟨236146694606277042008037869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157431129737518028005358579 236146694606277042008037869)
    ·
      refine ⟨88555010477353890753014201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236146694606277042008037869 88555010477353890753014201)
      ·
        refine ⟨66416257858015418064760651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88555010477353890753014201 66416257858015418064760651)
        ·
          refine ⟨99624386787023127097140977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66416257858015418064760651 99624386787023127097140977)
          ·
            refine ⟨74718290090267345322855733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 99624386787023127097140977 74718290090267345322855733)
            ·
              refine ⟨7004839695962563624017725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 74718290090267345322855733 7004839695962563624017725)
              ·
                refine ⟨2626814885985961359006647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7004839695962563624017725 2626814885985961359006647)
                ·
                  refine ⟨3940222328978942038509971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2626814885985961359006647 3940222328978942038509971)
                  ·
                    refine ⟨5910333493468413057764957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3940222328978942038509971 5910333493468413057764957)
                    ·
                      refine ⟨2216375060050654896661859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5910333493468413057764957 2216375060050654896661859)
                      ·
                        rfl

theorem cell23_4316375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 3, 1, 1, 3].length) (baseStart_4316375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316375 prefixEnd_4316375 := by exact prefixLift 4316375
  have htrace : WordTrace (prefixWord ++ tailWord_4316375) baseStart_4316375 baseEnd_4316375 := by
    simpa [prefixWord, tailWord_4316375, baseEnd_4316375] using wordTrace_append hprefix tailTrace_4316375
  have hstable : (prefixWord ++ tailWord_4316375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316375).length < 2 ^ (prefixWord ++ tailWord_4316375).sum := by decide
  have hdescent : baseEnd_4316375 < baseStart_4316375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316392 : List Nat := [2, 1, 4, 1, 2, 1, 5, 2, 1, 1, 3]
def baseStart_4316392 : Nat := 118140960795 + 4316392 * 2 ^ 59
def prefixEnd_4316392 : Nat := 4983230072969 + 3 ^ 40 * 4316392 * 2
def baseEnd_4316392 : Nat := 2216383789221781330149281

theorem tailTrace_4316392 : CollatzResearch.WordTrace tailWord_4316392 prefixEnd_4316392 2216383789221781330149281 := by
  unfold tailWord_4316392
  simp only [CollatzResearch.WordTrace]
  refine ⟨78715874889228219954363715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104954499852304293272484953 78715874889228219954363715)
  ·
    refine ⟨118073812333842329931545573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78715874889228219954363715 118073812333842329931545573)
    ·
      refine ⟨22138839812595436862164795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118073812333842329931545573 22138839812595436862164795)
      ·
        refine ⟨33208259718893155293247193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22138839812595436862164795 33208259718893155293247193)
        ·
          refine ⟨24906194789169866469935395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33208259718893155293247193 24906194789169866469935395)
          ·
            refine ⟨37359292183754799704903093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24906194789169866469935395 37359292183754799704903093)
            ·
              refine ⟨3502433642227012472334665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37359292183754799704903093 3502433642227012472334665)
              ·
                refine ⟨2626825231670259354250999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3502433642227012472334665 2626825231670259354250999)
                ·
                  refine ⟨3940237847505389031376499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2626825231670259354250999 3940237847505389031376499)
                  ·
                    refine ⟨5910356771258083547064749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3940237847505389031376499 5910356771258083547064749)
                    ·
                      refine ⟨2216383789221781330149281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5910356771258083547064749 2216383789221781330149281)
                      ·
                        rfl

theorem cell23_4316392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_4316392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316392 prefixEnd_4316392 := by exact prefixLift 4316392
  have htrace : WordTrace (prefixWord ++ tailWord_4316392) baseStart_4316392 baseEnd_4316392 := by
    simpa [prefixWord, tailWord_4316392, baseEnd_4316392] using wordTrace_append hprefix tailTrace_4316392
  have hstable : (prefixWord ++ tailWord_4316392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316392).length < 2 ^ (prefixWord ++ tailWord_4316392).sum := by decide
  have hdescent : baseEnd_4316392 < baseStart_4316392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316401 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 3, 2, 3]
def baseStart_4316401 : Nat := 118140960795 + 4316401 * 2 ^ 59
def prefixEnd_4316401 : Nat := 4983230072969 + 3 ^ 40 * 4316401 * 2
def baseEnd_4316401 : Nat := 2216388410547671794936739

theorem tailTrace_4316401 : CollatzResearch.WordTrace tailWord_4316401 prefixEnd_4316401 2216388410547671794936739 := by
  unfold tailWord_4316401
  simp only [CollatzResearch.WordTrace]
  refine ⟨157432078035423834445805057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104954718690282556297203371 157432078035423834445805057)
  ·
    refine ⟨118074058526567875834353793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157432078035423834445805057 118074058526567875834353793)
    ·
      refine ⟨88555543894925906875765345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118074058526567875834353793 88555543894925906875765345)
      ·
        refine ⟨66416657921194430156824009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88555543894925906875765345 66416657921194430156824009)
        ·
          refine ⟨49812493440895822617618007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66416657921194430156824009 49812493440895822617618007)
          ·
            refine ⟨74718740161343733926427011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49812493440895822617618007 74718740161343733926427011)
            ·
              refine ⟨112078110242015600889640517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74718740161343733926427011 112078110242015600889640517)
              ·
                refine ⟨21014645670377925166807597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 112078110242015600889640517 21014645670377925166807597)
                ·
                  refine ⟨7880492126391721937552849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21014645670377925166807597 7880492126391721937552849)
                  ·
                    refine ⟨5910369094793791453164637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7880492126391721937552849 5910369094793791453164637)
                    ·
                      refine ⟨2216388410547671794936739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5910369094793791453164637 2216388410547671794936739)
                      ·
                        rfl

theorem cell23_4316401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_4316401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316401 prefixEnd_4316401 := by exact prefixLift 4316401
  have htrace : WordTrace (prefixWord ++ tailWord_4316401) baseStart_4316401 baseEnd_4316401 := by
    simpa [prefixWord, tailWord_4316401, baseEnd_4316401] using wordTrace_append hprefix tailTrace_4316401
  have hstable : (prefixWord ++ tailWord_4316401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316401).length < 2 ^ (prefixWord ++ tailWord_4316401).sum := by decide
  have hdescent : baseEnd_4316401 < baseStart_4316401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316465 : List Nat := [1, 2, 2, 3, 3, 1, 2, 3, 2, 1, 3]
def baseStart_4316465 : Nat := 118140960795 + 4316465 * 2 ^ 59
def prefixEnd_4316465 : Nat := 4983230072969 + 3 ^ 40 * 4316465 * 2
def baseEnd_4316465 : Nat := 2216421273309559544536445

theorem tailTrace_4316465 : CollatzResearch.WordTrace tailWord_4316465 prefixEnd_4316465 2216421273309559544536445 := by
  unfold tailWord_4316465
  simp only [CollatzResearch.WordTrace]
  refine ⟨157434412307191973376134849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104956274871461315584089899 157434412307191973376134849)
  ·
    refine ⟨118075809230393980032101137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157434412307191973376134849 118075809230393980032101137)
    ·
      refine ⟨88556856922795485024075853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118075809230393980032101137 88556856922795485024075853)
      ·
        refine ⟨33208821346048306884028445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88556856922795485024075853 33208821346048306884028445)
        ·
          refine ⟨12453308004768115081510667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33208821346048306884028445 12453308004768115081510667)
          ·
            refine ⟨18679962007152172622266001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12453308004768115081510667 18679962007152172622266001)
            ·
              refine ⟨14009971505364129466699501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18679962007152172622266001 14009971505364129466699501)
              ·
                refine ⟨5253739314511548550012313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14009971505364129466699501 5253739314511548550012313)
                ·
                  refine ⟨3940304485883661412509235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5253739314511548550012313 3940304485883661412509235)
                  ·
                    refine ⟨5910456728825492118763853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3940304485883661412509235 5910456728825492118763853)
                    ·
                      refine ⟨2216421273309559544536445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5910456728825492118763853 2216421273309559544536445)
                      ·
                        rfl

theorem cell23_4316465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_4316465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316465 prefixEnd_4316465 := by exact prefixLift 4316465
  have htrace : WordTrace (prefixWord ++ tailWord_4316465) baseStart_4316465 baseEnd_4316465 := by
    simpa [prefixWord, tailWord_4316465, baseEnd_4316465] using wordTrace_append hprefix tailTrace_4316465
  have hstable : (prefixWord ++ tailWord_4316465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316465).length < 2 ^ (prefixWord ++ tailWord_4316465).sum := by decide
  have hdescent : baseEnd_4316465 < baseStart_4316465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316492 : List Nat := [2, 2, 1, 3, 2, 2, 4, 1, 1, 3, 2]
def baseStart_4316492 : Nat := 118140960795 + 4316492 * 2 ^ 59
def prefixEnd_4316492 : Nat := 4983230072969 + 3 ^ 40 * 4316492 * 2
def baseEnd_4316492 : Nat := 2216435137287230938898821

theorem tailTrace_4316492 : CollatzResearch.WordTrace tailWord_4316492 prefixEnd_4316492 2216435137287230938898821 := by
  unfold tailWord_4316492
  simp only [CollatzResearch.WordTrace]
  refine ⟨78717698539047078493683865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104956931385396104658245153 78717698539047078493683865)
  ·
    refine ⟨59038273904285308870262899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78717698539047078493683865 59038273904285308870262899)
    ·
      refine ⟨88557410856427963305394349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59038273904285308870262899 88557410856427963305394349)
      ·
        refine ⟨33209029071160486239522881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88557410856427963305394349 33209029071160486239522881)
        ·
          refine ⟨24906771803370364679642161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33209029071160486239522881 24906771803370364679642161)
          ·
            refine ⟨18680078852527773509731621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24906771803370364679642161 18680078852527773509731621)
            ·
              refine ⟨3502514784848957533074679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18680078852527773509731621 3502514784848957533074679)
              ·
                refine ⟨5253772177273436299612019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3502514784848957533074679 5253772177273436299612019)
                ·
                  refine ⟨7880658265910154449418029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5253772177273436299612019 7880658265910154449418029)
                  ·
                    refine ⟨2955246849716307918531761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7880658265910154449418029 2955246849716307918531761)
                    ·
                      refine ⟨2216435137287230938898821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2955246849716307918531761 2216435137287230938898821)
                      ·
                        rfl

theorem cell23_4316492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_4316492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316492 prefixEnd_4316492 := by exact prefixLift 4316492
  have htrace : WordTrace (prefixWord ++ tailWord_4316492) baseStart_4316492 baseEnd_4316492 := by
    simpa [prefixWord, tailWord_4316492, baseEnd_4316492] using wordTrace_append hprefix tailTrace_4316492
  have hstable : (prefixWord ++ tailWord_4316492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316492).length < 2 ^ (prefixWord ++ tailWord_4316492).sum := by decide
  have hdescent : baseEnd_4316492 < baseStart_4316492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316521 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 1, 5, 3]
def baseStart_4316521 : Nat := 118140960795 + 4316521 * 2 ^ 59
def prefixEnd_4316521 : Nat := 4983230072969 + 3 ^ 40 * 4316521 * 2
def baseEnd_4316521 : Nat := 2216450028226211325436187

theorem tailTrace_4316521 : CollatzResearch.WordTrace tailWord_4316521 prefixEnd_4316521 2216450028226211325436187 := by
  unfold tailWord_4316521
  simp only [CollatzResearch.WordTrace]
  refine ⟨157436454794989094940173417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104957636529992729960115611 157436454794989094940173417)
  ·
    refine ⟨118077341096241821205130063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157436454794989094940173417 118077341096241821205130063)
    ·
      refine ⟨177116011644362731807695095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118077341096241821205130063 177116011644362731807695095)
      ·
        refine ⟨265674017466544097711542643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177116011644362731807695095 265674017466544097711542643)
        ·
          refine ⟨398511026199816146567313965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265674017466544097711542643 398511026199816146567313965)
          ·
            refine ⟨149441634824931054962742737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 398511026199816146567313965 149441634824931054962742737)
            ·
              refine ⟨112081226118698291222057053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149441634824931054962742737 112081226118698291222057053)
              ·
                refine ⟨42030459794511859208271395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 112081226118698291222057053 42030459794511859208271395)
                ·
                  refine ⟨63045689691767788812407093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42030459794511859208271395 63045689691767788812407093)
                  ·
                    refine ⟨5910533408603230201163165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63045689691767788812407093 5910533408603230201163165)
                    ·
                      refine ⟨2216450028226211325436187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5910533408603230201163165 2216450028226211325436187)
                      ·
                        rfl

theorem cell23_4316521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 5, 3].length) (baseStart_4316521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316521 prefixEnd_4316521 := by exact prefixLift 4316521
  have htrace : WordTrace (prefixWord ++ tailWord_4316521) baseStart_4316521 baseEnd_4316521 := by
    simpa [prefixWord, tailWord_4316521, baseEnd_4316521] using wordTrace_append hprefix tailTrace_4316521
  have hstable : (prefixWord ++ tailWord_4316521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316521).length < 2 ^ (prefixWord ++ tailWord_4316521).sum := by decide
  have hdescent : baseEnd_4316521 < baseStart_4316521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316541 : List Nat := [1, 4, 1, 1, 2, 2, 1, 3, 1, 7]
def baseStart_4316541 : Nat := 118140960795 + 4316541 * 2 ^ 59
def prefixEnd_4316541 : Nat := 4983230072969 + 3 ^ 40 * 4316541 * 2
def baseEnd_4316541 : Nat := 738820099279767082395365

theorem tailTrace_4316541 : CollatzResearch.WordTrace tailWord_4316541 prefixEnd_4316541 738820099279767082395365 := by
  unfold tailWord_4316541
  simp only [CollatzResearch.WordTrace]
  refine ⟨157437184254916638355901477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104958122836611092237267651 157437184254916638355901477)
  ·
    refine ⟨29519472047796869691731527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157437184254916638355901477 29519472047796869691731527)
    ·
      refine ⟨44279208071695304537597291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29519472047796869691731527 44279208071695304537597291)
      ·
        refine ⟨66418812107542956806395937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44279208071695304537597291 66418812107542956806395937)
        ·
          refine ⟨49814109080657217604796953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66418812107542956806395937 49814109080657217604796953)
          ·
            refine ⟨37360581810492913203597715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49814109080657217604796953 37360581810492913203597715)
            ·
              refine ⟨56040872715739369805396573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37360581810492913203597715 56040872715739369805396573)
              ·
                refine ⟨21015327268402263677023715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56040872715739369805396573 21015327268402263677023715)
                ·
                  refine ⟨31522990902603395515535573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21015327268402263677023715 31522990902603395515535573)
                  ·
                    refine ⟨738820099279767082395365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31522990902603395515535573 738820099279767082395365)
                    ·
                      rfl

theorem cell23_4316541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_4316541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316541 prefixEnd_4316541 := by exact prefixLift 4316541
  have htrace : WordTrace (prefixWord ++ tailWord_4316541) baseStart_4316541 baseEnd_4316541 := by
    simpa [prefixWord, tailWord_4316541, baseEnd_4316541] using wordTrace_append hprefix tailTrace_4316541
  have hstable : (prefixWord ++ tailWord_4316541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316541).length < 2 ^ (prefixWord ++ tailWord_4316541).sum := by decide
  have hdescent : baseEnd_4316541 < baseStart_4316541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316542 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_4316542 : Nat := 118140960795 + 4316542 * 2 ^ 59
def prefixEnd_4316542 : Nat := 4983230072969 + 3 ^ 40 * 4316542 * 2
def baseEnd_4316542 : Nat := 2216460811319955743273591

theorem tailTrace_4316542 : CollatzResearch.WordTrace tailWord_4316542 prefixEnd_4316542 2216460811319955743273591 := by
  unfold tailWord_4316542
  simp only [CollatzResearch.WordTrace]
  refine ⟨19679652590989126940835985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104958147151942010351125253 19679652590989126940835985)
  ·
    refine ⟨14759739443241845205626989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19679652590989126940835985 14759739443241845205626989)
    ·
      refine ⟨5534902291215691952110121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14759739443241845205626989 5534902291215691952110121)
      ·
        refine ⟨4151176718411768964082591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5534902291215691952110121 4151176718411768964082591)
        ·
          refine ⟨6226765077617653446123887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4151176718411768964082591 6226765077617653446123887)
          ·
            refine ⟨9340147616426480169185831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6226765077617653446123887 9340147616426480169185831)
            ·
              refine ⟨14010221424639720253778747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9340147616426480169185831 14010221424639720253778747)
              ·
                refine ⟨21015332136959580380668121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14010221424639720253778747 21015332136959580380668121)
                ·
                  refine ⟨15761499102719685285501091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21015332136959580380668121 15761499102719685285501091)
                  ·
                    refine ⟨23642248654079527928251637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15761499102719685285501091 23642248654079527928251637)
                    ·
                      refine ⟨2216460811319955743273591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23642248654079527928251637 2216460811319955743273591)
                      ·
                        rfl

theorem cell23_4316542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_4316542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316542 prefixEnd_4316542 := by exact prefixLift 4316542
  have htrace : WordTrace (prefixWord ++ tailWord_4316542) baseStart_4316542 baseEnd_4316542 := by
    simpa [prefixWord, tailWord_4316542, baseEnd_4316542] using wordTrace_append hprefix tailTrace_4316542
  have hstable : (prefixWord ++ tailWord_4316542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316542).length < 2 ^ (prefixWord ++ tailWord_4316542).sum := by decide
  have hdescent : baseEnd_4316542 < baseStart_4316542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316562 : List Nat := [3, 2, 3, 3, 1, 2, 1, 1, 7]
def baseStart_4316562 : Nat := 118140960795 + 4316562 * 2 ^ 59
def prefixEnd_4316562 : Nat := 4983230072969 + 3 ^ 40 * 4316562 * 2
def baseEnd_4316562 : Nat := 246274564548116185002611

theorem tailTrace_4316562 : CollatzResearch.WordTrace tailWord_4316562 prefixEnd_4316562 246274564548116185002611 := by
  unfold tailWord_4316562
  simp only [CollatzResearch.WordTrace]
  refine ⟨39359487546960139735603985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104958633458560372628277293 39359487546960139735603985)
  ·
    refine ⟨29519615660220104801702989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39359487546960139735603985 29519615660220104801702989)
    ·
      refine ⟨11069855872582539300638621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29519615660220104801702989 11069855872582539300638621)
      ·
        refine ⟨4151195952218452237739483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11069855872582539300638621 4151195952218452237739483)
        ·
          refine ⟨6226793928327678356609225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4151195952218452237739483 6226793928327678356609225)
          ·
            refine ⟨4670095446245758767456919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6226793928327678356609225 4670095446245758767456919)
            ·
              refine ⟨7005143169368638151185379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4670095446245758767456919 7005143169368638151185379)
              ·
                refine ⟨10507714754052957226778069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7005143169368638151185379 10507714754052957226778069)
                ·
                  refine ⟨246274564548116185002611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10507714754052957226778069 246274564548116185002611)
                  ·
                    rfl

theorem cell23_4316562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_4316562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316562 prefixEnd_4316562 := by exact prefixLift 4316562
  have htrace : WordTrace (prefixWord ++ tailWord_4316562) baseStart_4316562 baseEnd_4316562 := by
    simpa [prefixWord, tailWord_4316562, baseEnd_4316562] using wordTrace_append hprefix tailTrace_4316562
  have hstable : (prefixWord ++ tailWord_4316562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316562).length < 2 ^ (prefixWord ++ tailWord_4316562).sum := by decide
  have hdescent : baseEnd_4316562 < baseStart_4316562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316588 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 3, 4]
def baseStart_4316588 : Nat := 118140960795 + 4316588 * 2 ^ 59
def prefixEnd_4316588 : Nat := 4983230072969 + 3 ^ 40 * 4316588 * 2
def baseEnd_4316588 : Nat := 738828143810020854432793

theorem tailTrace_4316588 : CollatzResearch.WordTrace tailWord_4316588 prefixEnd_4316588 738828143810020854432793 := by
  unfold tailWord_4316588
  simp only [CollatzResearch.WordTrace]
  refine ⟨78719449242873182691431209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104959265657164243588574945 78719449242873182691431209)
  ·
    refine ⟨59039586932154887018573407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78719449242873182691431209 59039586932154887018573407)
    ·
      refine ⟨88559380398232330527860111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59039586932154887018573407 88559380398232330527860111)
      ·
        refine ⟨132839070597348495791790167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88559380398232330527860111 132839070597348495791790167)
        ·
          refine ⟨199258605896022743687685251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132839070597348495791790167 199258605896022743687685251)
          ·
            refine ⟨298887908844034115531527877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199258605896022743687685251 298887908844034115531527877)
            ·
              refine ⟨56041482908256396662161477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 298887908844034115531527877 56041482908256396662161477)
              ·
                refine ⟨10507778045298074374155277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56041482908256396662161477 10507778045298074374155277)
                ·
                  refine ⟨3940416766986777890308229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10507778045298074374155277 3940416766986777890308229)
                  ·
                    refine ⟨738828143810020854432793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3940416766986777890308229 738828143810020854432793)
                    ·
                      rfl

theorem cell23_4316588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_4316588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316588 prefixEnd_4316588 := by exact prefixLift 4316588
  have htrace : WordTrace (prefixWord ++ tailWord_4316588) baseStart_4316588 baseEnd_4316588 := by
    simpa [prefixWord, tailWord_4316588, baseEnd_4316588] using wordTrace_append hprefix tailTrace_4316588
  have hstable : (prefixWord ++ tailWord_4316588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316588).length < 2 ^ (prefixWord ++ tailWord_4316588).sum := by decide
  have hdescent : baseEnd_4316588 < baseStart_4316588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316591 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 4]
def baseStart_4316591 : Nat := 118140960795 + 4316591 * 2 ^ 59
def prefixEnd_4316591 : Nat := 4983230072969 + 3 ^ 40 * 4316591 * 2
def baseEnd_4316591 : Nat := 2216485971872026051560865

theorem tailTrace_4316591 : CollatzResearch.WordTrace tailWord_4316591 prefixEnd_4316591 2216485971872026051560865 := by
  unfold tailWord_4316591
  simp only [CollatzResearch.WordTrace]
  refine ⟨157439007904735496895221627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104959338603156997930147751 157439007904735496895221627)
  ·
    refine ⟨236158511857103245342832441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157439007904735496895221627 236158511857103245342832441)
    ·
      refine ⟨177118883892827434007124331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236158511857103245342832441 177118883892827434007124331)
      ·
        refine ⟨265678325839241151010686497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177118883892827434007124331 265678325839241151010686497)
        ·
          refine ⟨199258744379430863258014873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 265678325839241151010686497 199258744379430863258014873)
          ·
            refine ⟨149444058284573147443511155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199258744379430863258014873 149444058284573147443511155)
            ·
              refine ⟨224166087426859721165266733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149444058284573147443511155 224166087426859721165266733)
              ·
                refine ⟨84062282785072395436975025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224166087426859721165266733 84062282785072395436975025)
                ·
                  refine ⟨63046712088804296577731269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84062282785072395436975025 63046712088804296577731269)
                  ·
                    refine ⟨11821258516650805608324613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 63046712088804296577731269 11821258516650805608324613)
                    ·
                      refine ⟨2216485971872026051560865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11821258516650805608324613 2216485971872026051560865)
                      ·
                        rfl

theorem cell23_4316591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_4316591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316591 prefixEnd_4316591 := by exact prefixLift 4316591
  have htrace : WordTrace (prefixWord ++ tailWord_4316591) baseStart_4316591 baseEnd_4316591 := by
    simpa [prefixWord, tailWord_4316591, baseEnd_4316591] using wordTrace_append hprefix tailTrace_4316591
  have hstable : (prefixWord ++ tailWord_4316591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316591).length < 2 ^ (prefixWord ++ tailWord_4316591).sum := by decide
  have hdescent : baseEnd_4316591 < baseStart_4316591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316618 : List Nat := [3, 1, 2, 1, 2, 3, 1, 4, 6]
def baseStart_4316618 : Nat := 118140960795 + 4316618 * 2 ^ 59
def prefixEnd_4316618 : Nat := 4983230072969 + 3 ^ 40 * 4316618 * 2
def baseEnd_4316618 : Nat := 246277759538855271769249

theorem tailTrace_4316618 : CollatzResearch.WordTrace tailWord_4316618 prefixEnd_4316618 246277759538855271769249 := by
  unfold tailWord_4316618
  simp only [CollatzResearch.WordTrace]
  refine ⟨39359998168909420126613627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104959995117091787004303005 39359998168909420126613627)
  ·
    refine ⟨59039997253364130189920441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39359998168909420126613627 59039997253364130189920441)
    ·
      refine ⟨44279997940023097642440331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59039997253364130189920441 44279997940023097642440331)
      ·
        refine ⟨66419996910034646463660497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44279997940023097642440331 66419996910034646463660497)
        ·
          refine ⟨49814997682525984847745373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66419996910034646463660497 49814997682525984847745373)
          ·
            refine ⟨18680624130947244317904515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 49814997682525984847745373 18680624130947244317904515)
            ·
              refine ⟨28020936196420866476856773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18680624130947244317904515 28020936196420866476856773)
              ·
                refine ⟨5253925536828912464410645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28020936196420866476856773 5253925536828912464410645)
                ·
                  refine ⟨246277759538855271769249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5253925536828912464410645 246277759538855271769249)
                  ·
                    rfl

theorem cell23_4316618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 6].length) (baseStart_4316618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316618 prefixEnd_4316618 := by exact prefixLift 4316618
  have htrace : WordTrace (prefixWord ++ tailWord_4316618) baseStart_4316618 baseEnd_4316618 := by
    simpa [prefixWord, tailWord_4316618, baseEnd_4316618] using wordTrace_append hprefix tailTrace_4316618
  have hstable : (prefixWord ++ tailWord_4316618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316618).length < 2 ^ (prefixWord ++ tailWord_4316618).sum := by decide
  have hdescent : baseEnd_4316618 < baseStart_4316618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316648 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 3, 5]
def baseStart_4316648 : Nat := 118140960795 + 4316648 * 2 ^ 59
def prefixEnd_4316648 : Nat := 4983230072969 + 3 ^ 40 * 4316648 * 2
def baseEnd_4316648 : Nat := 738838413423110776182701

theorem tailTrace_4316648 : CollatzResearch.WordTrace tailWord_4316648 prefixEnd_4316648 738838413423110776182701 := by
  unfold tailWord_4316648
  simp only [CollatzResearch.WordTrace]
  refine ⟨78720543432764497815023299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104960724577019330420031065 78720543432764497815023299)
  ·
    refine ⟨118080815149146746722534949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78720543432764497815023299 118080815149146746722534949)
    ·
      refine ⟨22140152840465015010475303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 118080815149146746722534949 22140152840465015010475303)
      ·
        refine ⟨33210229260697522515712955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22140152840465015010475303 33210229260697522515712955)
        ·
          refine ⟨49815343891046283773569433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33210229260697522515712955 49815343891046283773569433)
          ·
            refine ⟨37361507918284712830177075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 49815343891046283773569433 37361507918284712830177075)
            ·
              refine ⟨56042261877427069245265613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37361507918284712830177075 56042261877427069245265613)
              ·
                refine ⟨21015848204035150966974605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56042261877427069245265613 21015848204035150966974605)
                ·
                  refine ⟨7880943076513181612615477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21015848204035150966974605 7880943076513181612615477)
                  ·
                    refine ⟨738838413423110776182701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7880943076513181612615477 738838413423110776182701)
                    ·
                      rfl

theorem cell23_4316648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_4316648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316648 prefixEnd_4316648 := by exact prefixLift 4316648
  have htrace : WordTrace (prefixWord ++ tailWord_4316648) baseStart_4316648 baseEnd_4316648 := by
    simpa [prefixWord, tailWord_4316648, baseEnd_4316648] using wordTrace_append hprefix tailTrace_4316648
  have hstable : (prefixWord ++ tailWord_4316648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316648).length < 2 ^ (prefixWord ++ tailWord_4316648).sum := by decide
  have hdescent : baseEnd_4316648 < baseStart_4316648 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316679 : List Nat := [1, 1, 4, 3, 2, 1, 2, 4, 1, 1, 3]
def baseStart_4316679 : Nat := 118140960795 + 4316679 * 2 ^ 59
def prefixEnd_4316679 : Nat := 4983230072969 + 3 ^ 40 * 4316679 * 2
def baseEnd_4316679 : Nat := 2216531158169621707260461

theorem tailTrace_4316679 : CollatzResearch.WordTrace tailWord_4316679 prefixEnd_4316679 2216531158169621707260461 := by
  unfold tailWord_4316679
  simp only [CollatzResearch.WordTrace]
  refine ⟨157442217528416687924425091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104961478352277791949616727 157442217528416687924425091)
  ·
    refine ⟨236163326292625031886637637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157442217528416687924425091 236163326292625031886637637)
    ·
      refine ⟨44280623679867193478744557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 236163326292625031886637637 44280623679867193478744557)
      ·
        refine ⟨16605233879950197554529209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44280623679867193478744557 16605233879950197554529209)
        ·
          refine ⟨12453925409962648165896907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16605233879950197554529209 12453925409962648165896907)
          ·
            refine ⟨18680888114943972248845361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12453925409962648165896907 18680888114943972248845361)
            ·
              refine ⟨14010666086207979186634021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18680888114943972248845361 14010666086207979186634021)
              ·
                refine ⟨2626999891163996097493879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14010666086207979186634021 2626999891163996097493879)
                ·
                  refine ⟨3940499836745994146240819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2626999891163996097493879 3940499836745994146240819)
                  ·
                    refine ⟨5910749755118991219361229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3940499836745994146240819 5910749755118991219361229)
                    ·
                      refine ⟨2216531158169621707260461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5910749755118991219361229 2216531158169621707260461)
                      ·
                        rfl

theorem cell23_4316679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 4, 1, 1, 3].length) (baseStart_4316679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316679 prefixEnd_4316679 := by exact prefixLift 4316679
  have htrace : WordTrace (prefixWord ++ tailWord_4316679) baseStart_4316679 baseEnd_4316679 := by
    simpa [prefixWord, tailWord_4316679, baseEnd_4316679] using wordTrace_append hprefix tailTrace_4316679
  have hstable : (prefixWord ++ tailWord_4316679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316679).length < 2 ^ (prefixWord ++ tailWord_4316679).sum := by decide
  have hdescent : baseEnd_4316679 < baseStart_4316679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316752 : List Nat := [2, 1, 1, 1, 1, 3, 5, 3, 2, 1, 3]
def baseStart_4316752 : Nat := 118140960795 + 4316752 * 2 ^ 59
def prefixEnd_4316752 : Nat := 4983230072969 + 3 ^ 40 * 4316752 * 2
def baseEnd_4316752 : Nat := 2216568642257399921647625

theorem tailTrace_4316752 : CollatzResearch.WordTrace tailWord_4316752 prefixEnd_4316752 2216568642257399921647625 := by
  unfold tailWord_4316752
  simp only [CollatzResearch.WordTrace]
  refine ⟨78722440028576110695916255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104963253371434814261221673 78722440028576110695916255)
  ·
    refine ⟨118083660042864166043874383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78722440028576110695916255 118083660042864166043874383)
    ·
      refine ⟨177125490064296249065811575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118083660042864166043874383 177125490064296249065811575)
      ·
        refine ⟨265688235096444373598717363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177125490064296249065811575 265688235096444373598717363)
        ·
          refine ⟨398532352644666560398076045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265688235096444373598717363 398532352644666560398076045)
          ·
            refine ⟨149449632241749960149278517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 398532352644666560398076045 149449632241749960149278517)
            ·
              refine ⟨14010903022664058763994861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 149449632241749960149278517 14010903022664058763994861)
              ·
                refine ⟨5254088633499022036498073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14010903022664058763994861 5254088633499022036498073)
                ·
                  refine ⟨3940566475124266527373555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5254088633499022036498073 3940566475124266527373555)
                  ·
                    refine ⟨5910849712686399791060333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3940566475124266527373555 5910849712686399791060333)
                    ·
                      refine ⟨2216568642257399921647625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5910849712686399791060333 2216568642257399921647625)
                      ·
                        rfl

theorem cell23_4316752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3, 2, 1, 3].length) (baseStart_4316752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316752 prefixEnd_4316752 := by exact prefixLift 4316752
  have htrace : WordTrace (prefixWord ++ tailWord_4316752) baseStart_4316752 baseEnd_4316752 := by
    simpa [prefixWord, tailWord_4316752, baseEnd_4316752] using wordTrace_append hprefix tailTrace_4316752
  have hstable : (prefixWord ++ tailWord_4316752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316752).length < 2 ^ (prefixWord ++ tailWord_4316752).sum := by decide
  have hdescent : baseEnd_4316752 < baseStart_4316752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316768 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 4, 6]
def baseStart_4316768 : Nat := 118140960795 + 4316768 * 2 ^ 59
def prefixEnd_4316768 : Nat := 4983230072969 + 3 ^ 40 * 4316768 * 2
def baseEnd_4316768 : Nat := 738858952649290619682517

theorem tailTrace_4316768 : CollatzResearch.WordTrace tailWord_4316768 prefixEnd_4316768 738858952649290619682517 := by
  unfold tailWord_4316768
  simp only [CollatzResearch.WordTrace]
  refine ⟨78722731812547128062207479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104963642416729504082943305 78722731812547128062207479)
  ·
    refine ⟨118084097718820692093311219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78722731812547128062207479 118084097718820692093311219)
    ·
      refine ⟨177126146578231038139966829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118084097718820692093311219 177126146578231038139966829)
      ·
        refine ⟨66422304966836639302487561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177126146578231038139966829 66422304966836639302487561)
        ·
          refine ⟨49816728725127479476865671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 66422304966836639302487561 49816728725127479476865671)
          ·
            refine ⟨74725093087691219215298507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49816728725127479476865671 74725093087691219215298507)
            ·
              refine ⟨112087639631536828822947761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 74725093087691219215298507 112087639631536828822947761)
              ·
                refine ⟨84065729723652621617210821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112087639631536828822947761 84065729723652621617210821)
                ·
                  refine ⟨15762324323184866553227029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 84065729723652621617210821 15762324323184866553227029)
                  ·
                    refine ⟨738858952649290619682517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15762324323184866553227029 738858952649290619682517)
                    ·
                      rfl

theorem cell23_4316768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4, 6].length) (baseStart_4316768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316768 prefixEnd_4316768 := by exact prefixLift 4316768
  have htrace : WordTrace (prefixWord ++ tailWord_4316768) baseStart_4316768 baseEnd_4316768 := by
    simpa [prefixWord, tailWord_4316768, baseEnd_4316768] using wordTrace_append hprefix tailTrace_4316768
  have hstable : (prefixWord ++ tailWord_4316768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316768).length < 2 ^ (prefixWord ++ tailWord_4316768).sum := by decide
  have hdescent : baseEnd_4316768 < baseStart_4316768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316805 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 2, 2, 4]
def baseStart_4316805 : Nat := 118140960795 + 4316805 * 2 ^ 59
def prefixEnd_4316805 : Nat := 4983230072969 + 3 ^ 40 * 4316805 * 2
def baseEnd_4316805 : Nat := 2216595856732088214284881

theorem tailTrace_4316805 : CollatzResearch.WordTrace tailWord_4316805 prefixEnd_4316805 2216595856732088214284881 := by
  unfold tailWord_4316805
  simp only [CollatzResearch.WordTrace]
  refine ⟨157446813125960211443511869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104964542083973474295674579 157446813125960211443511869)
  ·
    refine ⟨59042554922235079291316951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157446813125960211443511869 59042554922235079291316951)
    ·
      refine ⟨88563832383352618936975427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59042554922235079291316951 88563832383352618936975427)
      ·
        refine ⟨132845748575028928405463141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88563832383352618936975427 132845748575028928405463141)
        ·
          refine ⟨24908577857817924076024339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 132845748575028928405463141 24908577857817924076024339)
          ·
            refine ⟨37362866786726886114036509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24908577857817924076024339 37362866786726886114036509)
            ·
              refine ⟨14011075045022582292763691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37362866786726886114036509 14011075045022582292763691)
              ·
                refine ⟨21016612567533873439145537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14011075045022582292763691 21016612567533873439145537)
                ·
                  refine ⟨15762459425650405079359153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21016612567533873439145537 15762459425650405079359153)
                  ·
                    refine ⟨11821844569237803809519365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15762459425650405079359153 11821844569237803809519365)
                    ·
                      refine ⟨2216595856732088214284881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11821844569237803809519365 2216595856732088214284881)
                      ·
                        rfl

theorem cell23_4316805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_4316805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316805 prefixEnd_4316805 := by exact prefixLift 4316805
  have htrace : WordTrace (prefixWord ++ tailWord_4316805) baseStart_4316805 baseEnd_4316805 := by
    simpa [prefixWord, tailWord_4316805, baseEnd_4316805] using wordTrace_append hprefix tailTrace_4316805
  have hstable : (prefixWord ++ tailWord_4316805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316805).length < 2 ^ (prefixWord ++ tailWord_4316805).sum := by decide
  have hdescent : baseEnd_4316805 < baseStart_4316805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316809 : List Nat := [1, 2, 1, 1, 4, 1, 4, 3, 2, 2, 2]
def baseStart_4316809 : Nat := 118140960795 + 4316809 * 2 ^ 59
def prefixEnd_4316809 : Nat := 4983230072969 + 3 ^ 40 * 4316809 * 2
def baseEnd_4316809 : Nat := 2216597910654706198634863

theorem tailTrace_4316809 : CollatzResearch.WordTrace tailWord_4316809 prefixEnd_4316809 2216597910654706198634863 := by
  unfold tailWord_4316809
  simp only [CollatzResearch.WordTrace]
  refine ⟨157446959017945720126657481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104964639345297146751104987 157446959017945720126657481)
  ·
    refine ⟨118085219263459290094993111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157446959017945720126657481 118085219263459290094993111)
    ·
      refine ⟨177127828895188935142489667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118085219263459290094993111 177127828895188935142489667)
      ·
        refine ⟨265691743342783402713734501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177127828895188935142489667 265691743342783402713734501)
        ·
          refine ⟨49817201876771888008825219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 265691743342783402713734501 49817201876771888008825219)
          ·
            refine ⟨74725802815157832013237829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49817201876771888008825219 74725802815157832013237829)
            ·
              refine ⟨14011088027842093502482093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74725802815157832013237829 14011088027842093502482093)
              ·
                refine ⟨5254158010440785063430785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14011088027842093502482093 5254158010440785063430785)
                ·
                  refine ⟨3940618507830588797573089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5254158010440785063430785 3940618507830588797573089)
                  ·
                    refine ⟨2955463880872941598179817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3940618507830588797573089 2955463880872941598179817)
                    ·
                      refine ⟨2216597910654706198634863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2955463880872941598179817 2216597910654706198634863)
                      ·
                        rfl

theorem cell23_4316809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 2, 2].length) (baseStart_4316809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316809 prefixEnd_4316809 := by exact prefixLift 4316809
  have htrace : WordTrace (prefixWord ++ tailWord_4316809) baseStart_4316809 baseEnd_4316809 := by
    simpa [prefixWord, tailWord_4316809, baseEnd_4316809] using wordTrace_append hprefix tailTrace_4316809
  have hstable : (prefixWord ++ tailWord_4316809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316809).length < 2 ^ (prefixWord ++ tailWord_4316809).sum := by decide
  have hdescent : baseEnd_4316809 < baseStart_4316809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316832 : List Nat := [2, 1, 1, 4, 3, 1, 1, 5, 5]
def baseStart_4316832 : Nat := 118140960795 + 4316832 * 2 ^ 59
def prefixEnd_4316832 : Nat := 4983230072969 + 3 ^ 40 * 4316832 * 2
def baseEnd_4316832 : Nat := 246289968967751067627473

theorem tailTrace_4316832 : CollatzResearch.WordTrace tailWord_4316832 prefixEnd_4316832 246289968967751067627473 := by
  unfold tailWord_4316832
  simp only [CollatzResearch.WordTrace]
  refine ⟨78723898948431197527372375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104965198597908263369829833 78723898948431197527372375)
  ·
    refine ⟨118085848422646796291058563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78723898948431197527372375 118085848422646796291058563)
    ·
      refine ⟨177128772633970194436587845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118085848422646796291058563 177128772633970194436587845)
      ·
        refine ⟨33211644868869411456860221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177128772633970194436587845 33211644868869411456860221)
        ·
          refine ⟨12454366825826029296322583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33211644868869411456860221 12454366825826029296322583)
          ·
            refine ⟨18681550238739043944483875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12454366825826029296322583 18681550238739043944483875)
            ·
              refine ⟨28022325358108565916725813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18681550238739043944483875 28022325358108565916725813)
              ·
                refine ⟨2627093002322678054693045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28022325358108565916725813 2627093002322678054693045)
                ·
                  refine ⟨246289968967751067627473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2627093002322678054693045 246289968967751067627473)
                  ·
                    rfl

theorem cell23_4316832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 5].length) (baseStart_4316832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316832 prefixEnd_4316832 := by exact prefixLift 4316832
  have htrace : WordTrace (prefixWord ++ tailWord_4316832) baseStart_4316832 baseEnd_4316832 := by
    simpa [prefixWord, tailWord_4316832, baseEnd_4316832] using wordTrace_append hprefix tailTrace_4316832
  have hstable : (prefixWord ++ tailWord_4316832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316832).length < 2 ^ (prefixWord ++ tailWord_4316832).sum := by decide
  have hdescent : baseEnd_4316832 < baseStart_4316832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316882 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_4316882 : Nat := 118140960795 + 4316882 * 2 ^ 59
def prefixEnd_4316882 : Nat := 4983230072969 + 3 ^ 40 * 4316882 * 2
def baseEnd_4316882 : Nat := 2216635394742484413022027

theorem tailTrace_4316882 : CollatzResearch.WordTrace tailWord_4316882 prefixEnd_4316882 2216635394742484413022027 := by
  unfold tailWord_4316882
  simp only [CollatzResearch.WordTrace]
  refine ⟨39362405386670313398516225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104966414364454169062709933 39362405386670313398516225)
  ·
    refine ⟨29521804040002735048887169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39362405386670313398516225 29521804040002735048887169)
    ·
      refine ⟨22141353030002051286665377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29521804040002735048887169 22141353030002051286665377)
      ·
        refine ⟨16606014772501538464999033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22141353030002051286665377 16606014772501538464999033)
        ·
          refine ⟨12454511079376153848749275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16606014772501538464999033 12454511079376153848749275)
          ·
            refine ⟨18681766619064230773123913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12454511079376153848749275 18681766619064230773123913)
            ·
              refine ⟨14011324964298173079842935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18681766619064230773123913 14011324964298173079842935)
              ·
                refine ⟨21016987446447259619764403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14011324964298173079842935 21016987446447259619764403)
                ·
                  refine ⟨31525481169670889429646605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21016987446447259619764403 31525481169670889429646605)
                  ·
                    refine ⟨11822055438626583536117477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 31525481169670889429646605 11822055438626583536117477)
                    ·
                      refine ⟨2216635394742484413022027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11822055438626583536117477 2216635394742484413022027)
                      ·
                        rfl

theorem cell23_4316882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_4316882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316882 prefixEnd_4316882 := by exact prefixLift 4316882
  have htrace : WordTrace (prefixWord ++ tailWord_4316882) baseStart_4316882 baseEnd_4316882 := by
    simpa [prefixWord, tailWord_4316882, baseEnd_4316882] using wordTrace_append hprefix tailTrace_4316882
  have hstable : (prefixWord ++ tailWord_4316882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316882).length < 2 ^ (prefixWord ++ tailWord_4316882).sum := by decide
  have hdescent : baseEnd_4316882 < baseStart_4316882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316899 : List Nat := [1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 4]
def baseStart_4316899 : Nat := 118140960795 + 4316899 * 2 ^ 59
def prefixEnd_4316899 : Nat := 4983230072969 + 3 ^ 40 * 4316899 * 2
def baseEnd_4316899 : Nat := 2216644123913610846509449

theorem tailTrace_4316899 : CollatzResearch.WordTrace tailWord_4316899 prefixEnd_4316899 2216644123913610846509449 := by
  unfold tailWord_4316899
  simp only [CollatzResearch.WordTrace]
  refine ⟨157450241587619665497433751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104966827725079776998289167 157450241587619665497433751)
  ·
    refine ⟨236175362381429498246150627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157450241587619665497433751 236175362381429498246150627)
    ·
      refine ⟨354263043572144247369225941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236175362381429498246150627 354263043572144247369225941)
      ·
        refine ⟨8303040083722130797716233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 354263043572144247369225941 8303040083722130797716233)
        ·
          refine ⟨6227280062791598098287175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8303040083722130797716233 6227280062791598098287175)
          ·
            refine ⟨9340920094187397147430763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6227280062791598098287175 9340920094187397147430763)
            ·
              refine ⟨14011380141281095721146145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9340920094187397147430763 14011380141281095721146145)
              ·
                refine ⟨10508535105960821790859609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14011380141281095721146145 10508535105960821790859609)
                ·
                  refine ⟨7881401329470616343144707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10508535105960821790859609 7881401329470616343144707)
                  ·
                    refine ⟨11822101994205924514717061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7881401329470616343144707 11822101994205924514717061)
                    ·
                      refine ⟨2216644123913610846509449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11822101994205924514717061 2216644123913610846509449)
                      ·
                        rfl

theorem cell23_4316899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_4316899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316899 prefixEnd_4316899 := by exact prefixLift 4316899
  have htrace : WordTrace (prefixWord ++ tailWord_4316899) baseStart_4316899 baseEnd_4316899 := by
    simpa [prefixWord, tailWord_4316899, baseEnd_4316899] using wordTrace_append hprefix tailTrace_4316899
  have hstable : (prefixWord ++ tailWord_4316899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316899).length < 2 ^ (prefixWord ++ tailWord_4316899).sum := by decide
  have hdescent : baseEnd_4316899 < baseStart_4316899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316905 : List Nat := [1, 2, 1, 1, 1, 2, 3, 6, 6]
def baseStart_4316905 : Nat := 118140960795 + 4316905 * 2 ^ 59
def prefixEnd_4316905 : Nat := 4983230072969 + 3 ^ 40 * 4316905 * 2
def baseEnd_4316905 : Nat := 246294133866393091448269

theorem tailTrace_4316905 : CollatzResearch.WordTrace tailWord_4316905 prefixEnd_4316905 246294133866393091448269 := by
  unfold tailWord_4316905
  simp only [CollatzResearch.WordTrace]
  refine ⟨157450460425597928522152169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104966973617065285681434779 157450460425597928522152169)
  ·
    refine ⟨118087845319198446391614127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157450460425597928522152169 118087845319198446391614127)
    ·
      refine ⟨177131767978797669587421191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118087845319198446391614127 177131767978797669587421191)
      ·
        refine ⟨265697651968196504381131787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177131767978797669587421191 265697651968196504381131787)
        ·
          refine ⟨398546477952294756571697681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265697651968196504381131787 398546477952294756571697681)
          ·
            refine ⟨298909858464221067428773261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398546477952294756571697681 298909858464221067428773261)
            ·
              refine ⟨112091196924082900285789973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 298909858464221067428773261 112091196924082900285789973)
              ·
                refine ⟨5254274855816385950896405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 112091196924082900285789973 5254274855816385950896405)
                ·
                  refine ⟨246294133866393091448269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5254274855816385950896405 246294133866393091448269)
                  ·
                    rfl

theorem cell23_4316905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 6, 6].length) (baseStart_4316905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316905 prefixEnd_4316905 := by exact prefixLift 4316905
  have htrace : WordTrace (prefixWord ++ tailWord_4316905) baseStart_4316905 baseEnd_4316905 := by
    simpa [prefixWord, tailWord_4316905, baseEnd_4316905] using wordTrace_append hprefix tailTrace_4316905
  have hstable : (prefixWord ++ tailWord_4316905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316905).length < 2 ^ (prefixWord ++ tailWord_4316905).sum := by decide
  have hdescent : baseEnd_4316905 < baseStart_4316905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316909 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_4316909 : Nat := 118140960795 + 4316909 * 2 ^ 59
def prefixEnd_4316909 : Nat := 4983230072969 + 3 ^ 40 * 4316909 * 2
def baseEnd_4316909 : Nat := 738883086240051935794801

theorem tailTrace_4316909 : CollatzResearch.WordTrace tailWord_4316909 prefixEnd_4316909 738883086240051935794801 := by
  unfold tailWord_4316909
  simp only [CollatzResearch.WordTrace]
  refine ⟨157450606317583437205297781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104967070878388958136865187 157450606317583437205297781)
  ·
    refine ⟨14760994342273447237996667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 157450606317583437205297781 14760994342273447237996667)
    ·
      refine ⟨22141491513410170856995001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14760994342273447237996667 22141491513410170856995001)
      ·
        refine ⟨16606118635057628142746251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22141491513410170856995001 16606118635057628142746251)
        ·
          refine ⟨24909177952586442214119377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16606118635057628142746251 24909177952586442214119377)
          ·
            refine ⟨18681883464439831660589533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24909177952586442214119377 18681883464439831660589533)
            ·
              refine ⟨7005706299164936872721075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18681883464439831660589533 7005706299164936872721075)
              ·
                refine ⟨10508559448747405309081613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7005706299164936872721075 10508559448747405309081613)
                ·
                  refine ⟨3940709793280276990905605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10508559448747405309081613 3940709793280276990905605)
                  ·
                    refine ⟨738883086240051935794801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3940709793280276990905605 738883086240051935794801)
                    ·
                      rfl

theorem cell23_4316909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_4316909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316909 prefixEnd_4316909 := by exact prefixLift 4316909
  have htrace : WordTrace (prefixWord ++ tailWord_4316909) baseStart_4316909 baseEnd_4316909 := by
    simpa [prefixWord, tailWord_4316909, baseEnd_4316909] using wordTrace_append hprefix tailTrace_4316909
  have hstable : (prefixWord ++ tailWord_4316909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316909).length < 2 ^ (prefixWord ++ tailWord_4316909).sum := by decide
  have hdescent : baseEnd_4316909 < baseStart_4316909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316952 : List Nat := [2, 1, 2, 3, 1, 1, 2, 5, 1, 5]
def baseStart_4316952 : Nat := 118140960795 + 4316952 * 2 ^ 59
def prefixEnd_4316952 : Nat := 4983230072969 + 3 ^ 40 * 4316952 * 2
def baseEnd_4316952 : Nat := 738890446129433046382235

theorem tailTrace_4316952 : CollatzResearch.WordTrace tailWord_4316952 prefixEnd_4316952 738890446129433046382235 := by
  unfold tailWord_4316952
  simp only [CollatzResearch.WordTrace]
  refine ⟨78726087328213827774556555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104968116437618437032742073 78726087328213827774556555)
  ·
    refine ⟨118089130992320741661834833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78726087328213827774556555 118089130992320741661834833)
    ·
      refine ⟨88566848244240556246376125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118089130992320741661834833 88566848244240556246376125)
      ·
        refine ⟨33212568091590208592391047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 88566848244240556246376125 33212568091590208592391047)
        ·
          refine ⟨49818852137385312888586571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33212568091590208592391047 49818852137385312888586571)
          ·
            refine ⟨74728278206077969332879857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49818852137385312888586571 74728278206077969332879857)
            ·
              refine ⟨56046208654558476999659893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74728278206077969332879857 56046208654558476999659893)
              ·
                refine ⟨5254332061364857218718115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56046208654558476999659893 5254332061364857218718115)
                ·
                  refine ⟨7881498092047285828077173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5254332061364857218718115 7881498092047285828077173)
                  ·
                    refine ⟨738890446129433046382235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7881498092047285828077173 738890446129433046382235)
                    ·
                      rfl

theorem cell23_4316952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_4316952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316952 prefixEnd_4316952 := by exact prefixLift 4316952
  have htrace : WordTrace (prefixWord ++ tailWord_4316952) baseStart_4316952 baseEnd_4316952 := by
    simpa [prefixWord, tailWord_4316952, baseEnd_4316952] using wordTrace_append hprefix tailTrace_4316952
  have hstable : (prefixWord ++ tailWord_4316952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316952).length < 2 ^ (prefixWord ++ tailWord_4316952).sum := by decide
  have hdescent : baseEnd_4316952 < baseStart_4316952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316959 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 2, 3, 2]
def baseStart_4316959 : Nat := 118140960795 + 4316959 * 2 ^ 59
def prefixEnd_4316959 : Nat := 4983230072969 + 3 ^ 40 * 4316959 * 2
def baseEnd_4316959 : Nat := 2216674932752880611759173

theorem tailTrace_4316959 : CollatzResearch.WordTrace tailWord_4316959 prefixEnd_4316959 2216674932752880611759173 := by
  unfold tailWord_4316959
  simp only [CollatzResearch.WordTrace]
  refine ⟨157452429967402295744617931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104968286644934863829745287 157452429967402295744617931)
  ·
    refine ⟨236178644951103443616926897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157452429967402295744617931 236178644951103443616926897)
    ·
      refine ⟨177133983713327582712695173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236178644951103443616926897 177133983713327582712695173)
      ·
        refine ⟨33212621946248921758630345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 177133983713327582712695173 33212621946248921758630345)
        ·
          refine ⟨24909466459686691318972759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33212621946248921758630345 24909466459686691318972759)
          ·
            refine ⟨37364199689530036978459139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24909466459686691318972759 37364199689530036978459139)
            ·
              refine ⟨56046299534295055467688709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37364199689530036978459139 56046299534295055467688709)
              ·
                refine ⟨10508681162680322900191633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56046299534295055467688709 10508681162680322900191633)
                ·
                  refine ⟨7881510872010242175143725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10508681162680322900191633 7881510872010242175143725)
                  ·
                    refine ⟨2955566577003840815678897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7881510872010242175143725 2955566577003840815678897)
                    ·
                      refine ⟨2216674932752880611759173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2955566577003840815678897 2216674932752880611759173)
                      ·
                        rfl

theorem cell23_4316959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_4316959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316959 prefixEnd_4316959 := by exact prefixLift 4316959
  have htrace : WordTrace (prefixWord ++ tailWord_4316959) baseStart_4316959 baseEnd_4316959 := by
    simpa [prefixWord, tailWord_4316959, baseEnd_4316959] using wordTrace_append hprefix tailTrace_4316959
  have hstable : (prefixWord ++ tailWord_4316959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316959).length < 2 ^ (prefixWord ++ tailWord_4316959).sum := by decide
  have hdescent : baseEnd_4316959 < baseStart_4316959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316972 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 4]
def baseStart_4316972 : Nat := 118140960795 + 4316972 * 2 ^ 59
def prefixEnd_4316972 : Nat := 4983230072969 + 3 ^ 40 * 4316972 * 2
def baseEnd_4316972 : Nat := 2216681608001389060896613

theorem tailTrace_4316972 : CollatzResearch.WordTrace tailWord_4316972 prefixEnd_4316972 2216681608001389060896613 := by
  unfold tailWord_4316972
  simp only [CollatzResearch.WordTrace]
  refine ⟨78726452058177599482420585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104968602744236799309894113 78726452058177599482420585)
  ·
    refine ⟨59044839043633199611815439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78726452058177599482420585 59044839043633199611815439)
    ·
      refine ⟨88567258565449799417723159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59044839043633199611815439 88567258565449799417723159)
      ·
        refine ⟨132850887848174699126584739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88567258565449799417723159 132850887848174699126584739)
        ·
          refine ⟨199276331772262048689877109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132850887848174699126584739 199276331772262048689877109)
          ·
            refine ⟨18682156103649567064675979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 199276331772262048689877109 18682156103649567064675979)
            ·
              refine ⟨28023234155474350597013969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18682156103649567064675979 28023234155474350597013969)
              ·
                refine ⟨21017425616605762947760477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28023234155474350597013969 21017425616605762947760477)
                ·
                  refine ⟨7881534606227161105410179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21017425616605762947760477 7881534606227161105410179)
                  ·
                    refine ⟨11822301909340741658115269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7881534606227161105410179 11822301909340741658115269)
                    ·
                      refine ⟨2216681608001389060896613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11822301909340741658115269 2216681608001389060896613)
                      ·
                        rfl

theorem cell23_4316972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_4316972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316972 prefixEnd_4316972 := by exact prefixLift 4316972
  have htrace : WordTrace (prefixWord ++ tailWord_4316972) baseStart_4316972 baseEnd_4316972 := by
    simpa [prefixWord, tailWord_4316972, baseEnd_4316972] using wordTrace_append hprefix tailTrace_4316972
  have hstable : (prefixWord ++ tailWord_4316972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316972).length < 2 ^ (prefixWord ++ tailWord_4316972).sum := by decide
  have hdescent : baseEnd_4316972 < baseStart_4316972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4316989 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_4316989 : Nat := 118140960795 + 4316989 * 2 ^ 59
def prefixEnd_4316989 : Nat := 4983230072969 + 3 ^ 40 * 4316989 * 2
def baseEnd_4316989 : Nat := 2216690337172515494384035

theorem tailTrace_4316989 : CollatzResearch.WordTrace tailWord_4316989 prefixEnd_4316989 2216690337172515494384035 := by
  unfold tailWord_4316989
  simp only [CollatzResearch.WordTrace]
  refine ⟨157453524157293610868210021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104969016104862407245473347 157453524157293610868210021)
  ·
    refine ⟨29522535779492552037789379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 157453524157293610868210021 29522535779492552037789379)
    ·
      refine ⟨44283803669238828056684069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29522535779492552037789379 44283803669238828056684069)
      ·
        refine ⟨8303213187982280260628263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44283803669238828056684069 8303213187982280260628263)
        ·
          refine ⟨12454819781973420390942395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8303213187982280260628263 12454819781973420390942395)
          ·
            refine ⟨18682229672960130586413593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12454819781973420390942395 18682229672960130586413593)
            ·
              refine ⟨14011672254720097939810195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18682229672960130586413593 14011672254720097939810195)
              ·
                refine ⟨21017508382080146909715293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14011672254720097939810195 21017508382080146909715293)
                ·
                  refine ⟨7881565643280055091143235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21017508382080146909715293 7881565643280055091143235)
                  ·
                    refine ⟨11822348464920082636714853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7881565643280055091143235 11822348464920082636714853)
                    ·
                      refine ⟨2216690337172515494384035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11822348464920082636714853 2216690337172515494384035)
                      ·
                        rfl

theorem cell23_4316989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_4316989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4316989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4316989 prefixEnd_4316989 := by exact prefixLift 4316989
  have htrace : WordTrace (prefixWord ++ tailWord_4316989) baseStart_4316989 baseEnd_4316989 := by
    simpa [prefixWord, tailWord_4316989, baseEnd_4316989] using wordTrace_append hprefix tailTrace_4316989
  have hstable : (prefixWord ++ tailWord_4316989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4316989).length < 2 ^ (prefixWord ++ tailWord_4316989).sum := by decide
  have hdescent : baseEnd_4316989 < baseStart_4316989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4316989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317002 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 1, 2, 4]
def baseStart_4317002 : Nat := 118140960795 + 4317002 * 2 ^ 59
def prefixEnd_4317002 : Nat := 4983230072969 + 3 ^ 40 * 4317002 * 2
def baseEnd_4317002 : Nat := 2216697012421023943521475

theorem tailTrace_4317002 : CollatzResearch.WordTrace tailWord_4317002 prefixEnd_4317002 2216697012421023943521475 := by
  unfold tailWord_4317002
  simp only [CollatzResearch.WordTrace]
  refine ⟨39363499576561628522108315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104969332204164342725622173 39363499576561628522108315)
  ·
    refine ⟨59045249364842442783162473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39363499576561628522108315 59045249364842442783162473)
    ·
      refine ⟨44283937023631832087371855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59045249364842442783162473 44283937023631832087371855)
      ·
        refine ⟨66425905535447748131057783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44283937023631832087371855 66425905535447748131057783)
        ·
          refine ⟨99638858303171622196586675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66425905535447748131057783 99638858303171622196586675)
          ·
            refine ⟨149458287454757433294880013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99638858303171622196586675 149458287454757433294880013)
            ·
              refine ⟨56046857795534037485580005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 149458287454757433294880013 56046857795534037485580005)
              ·
                refine ⟨10508785836662632028546251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56046857795534037485580005 10508785836662632028546251)
                ·
                  refine ⟨15763178754993948042819377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10508785836662632028546251 15763178754993948042819377)
                  ·
                    refine ⟨11822384066245461032114533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15763178754993948042819377 11822384066245461032114533)
                    ·
                      refine ⟨2216697012421023943521475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11822384066245461032114533 2216697012421023943521475)
                      ·
                        rfl

theorem cell23_4317002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_4317002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317002 prefixEnd_4317002 := by exact prefixLift 4317002
  have htrace : WordTrace (prefixWord ++ tailWord_4317002) baseStart_4317002 baseEnd_4317002 := by
    simpa [prefixWord, tailWord_4317002, baseEnd_4317002] using wordTrace_append hprefix tailTrace_4317002
  have hstable : (prefixWord ++ tailWord_4317002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317002).length < 2 ^ (prefixWord ++ tailWord_4317002).sum := by decide
  have hdescent : baseEnd_4317002 < baseStart_4317002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317012 : List Nat := [2, 4, 1, 1, 3, 2, 10]
def baseStart_4317012 : Nat := 118140960795 + 4317012 * 2 ^ 59
def prefixEnd_4317012 : Nat := 4983230072969 + 3 ^ 40 * 4317012 * 2
def baseEnd_4317012 : Nat := 27366693175648998819709

theorem tailTrace_4317012 : CollatzResearch.WordTrace tailWord_4317012 prefixEnd_4317012 27366693175648998819709 := by
  unfold tailWord_4317012
  simp only [CollatzResearch.WordTrace]
  refine ⟨78727181518105142898148645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104969575357473523864198193 78727181518105142898148645)
  ·
    refine ⟨14761346534644714293402871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 78727181518105142898148645 14761346534644714293402871)
    ·
      refine ⟨22142019801967071440104307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14761346534644714293402871 22142019801967071440104307)
      ·
        refine ⟨33213029702950607160156461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22142019801967071440104307 33213029702950607160156461)
        ·
          refine ⟨12454886138606477685058673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33213029702950607160156461 12454886138606477685058673)
          ·
            refine ⟨9341164603954858263794005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12454886138606477685058673 9341164603954858263794005)
            ·
              refine ⟨27366693175648998819709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9341164603954858263794005 27366693175648998819709)
              ·
                rfl

theorem cell23_4317012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 10].length) (baseStart_4317012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317012 prefixEnd_4317012 := by exact prefixLift 4317012
  have htrace : WordTrace (prefixWord ++ tailWord_4317012) baseStart_4317012 baseEnd_4317012 := by
    simpa [prefixWord, tailWord_4317012, baseEnd_4317012] using wordTrace_append hprefix tailTrace_4317012
  have hstable : (prefixWord ++ tailWord_4317012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317012).length < 2 ^ (prefixWord ++ tailWord_4317012).sum := by decide
  have hdescent : baseEnd_4317012 < baseStart_4317012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317023 : List Nat := [1, 1, 2, 3, 1, 4, 2, 4, 1, 2, 2]
def baseStart_4317023 : Nat := 118140960795 + 4317023 * 2 ^ 59
def prefixEnd_4317023 : Nat := 4983230072969 + 3 ^ 40 * 4317023 * 2
def baseEnd_4317023 : Nat := 2216707795514768361358879

theorem tailTrace_4317023 : CollatzResearch.WordTrace tailWord_4317023 prefixEnd_4317023 2216707795514768361358879 := by
  unfold tailWord_4317023
  simp only [CollatzResearch.WordTrace]
  refine ⟨157454764239170434674947723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104969842826113623116631815 157454764239170434674947723)
  ·
    refine ⟨236182146358755652012421585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157454764239170434674947723 236182146358755652012421585)
    ·
      refine ⟨177136609769066739009316189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236182146358755652012421585 177136609769066739009316189)
      ·
        refine ⟨66426228663400027128493571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 177136609769066739009316189 66426228663400027128493571)
        ·
          refine ⟨99639342995100040692740357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66426228663400027128493571 99639342995100040692740357)
          ·
            refine ⟨18682376811581257629888817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99639342995100040692740357 18682376811581257629888817)
            ·
              refine ⟨14011782608685943222416613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18682376811581257629888817 14011782608685943222416613)
              ·
                refine ⟨2627209239128614354203115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14011782608685943222416613 2627209239128614354203115)
                ·
                  refine ⟨3940813858692921531304673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2627209239128614354203115 3940813858692921531304673)
                  ·
                    refine ⟨2955610394019691148478505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3940813858692921531304673 2955610394019691148478505)
                    ·
                      refine ⟨2216707795514768361358879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2955610394019691148478505 2216707795514768361358879)
                      ·
                        rfl

theorem cell23_4317023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_4317023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317023 prefixEnd_4317023 := by exact prefixLift 4317023
  have htrace : WordTrace (prefixWord ++ tailWord_4317023) baseStart_4317023 baseEnd_4317023 := by
    simpa [prefixWord, tailWord_4317023, baseEnd_4317023] using wordTrace_append hprefix tailTrace_4317023
  have hstable : (prefixWord ++ tailWord_4317023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317023).length < 2 ^ (prefixWord ++ tailWord_4317023).sum := by decide
  have hdescent : baseEnd_4317023 < baseStart_4317023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317119 : List Nat := [1, 1, 2, 2, 2, 1, 4, 5, 5]
def baseStart_4317119 : Nat := 118140960795 + 4317119 * 2 ^ 59
def prefixEnd_4317119 : Nat := 4983230072969 + 3 ^ 40 * 4317119 * 2
def baseEnd_4317119 : Nat := 246306343295288887306493

theorem tailTrace_4317119 : CollatzResearch.WordTrace tailWord_4317119 prefixEnd_4317119 246306343295288887306493 := by
  unfold tailWord_4317119
  simp only [CollatzResearch.WordTrace]
  refine ⟨157458265646822643070442411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104972177097881762046961607 157458265646822643070442411)
  ·
    refine ⟨236187398470233964605663617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157458265646822643070442411 236187398470233964605663617)
    ·
      refine ⟨177140548852675473454247713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236187398470233964605663617 177140548852675473454247713)
      ·
        refine ⟨132855411639506605090685785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177140548852675473454247713 132855411639506605090685785)
        ·
          refine ⟨99641558729629953818014339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132855411639506605090685785 99641558729629953818014339)
          ·
            refine ⟨149462338094444930727021509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99641558729629953818014339 149462338094444930727021509)
            ·
              refine ⟨28024188392708424511316533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 149462338094444930727021509 28024188392708424511316533)
              ·
                refine ⟨2627267661816414797935925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28024188392708424511316533 2627267661816414797935925)
                ·
                  refine ⟨246306343295288887306493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2627267661816414797935925 246306343295288887306493)
                  ·
                    rfl

theorem cell23_4317119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 5].length) (baseStart_4317119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317119 prefixEnd_4317119 := by exact prefixLift 4317119
  have htrace : WordTrace (prefixWord ++ tailWord_4317119) baseStart_4317119 baseEnd_4317119 := by
    simpa [prefixWord, tailWord_4317119, baseEnd_4317119] using wordTrace_append hprefix tailTrace_4317119
  have hstable : (prefixWord ++ tailWord_4317119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317119).length < 2 ^ (prefixWord ++ tailWord_4317119).sum := by decide
  have hdescent : baseEnd_4317119 < baseStart_4317119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317136 : List Nat := [2, 1, 1, 1, 1, 2, 8, 2, 5]
def baseStart_4317136 : Nat := 118140960795 + 4317136 * 2 ^ 59
def prefixEnd_4317136 : Nat := 4983230072969 + 3 ^ 40 * 4317136 * 2
def baseEnd_4317136 : Nat := 246307313203191824360651

theorem tailTrace_4317136 : CollatzResearch.WordTrace tailWord_4317136 prefixEnd_4317136 246307313203191824360651 := by
  unfold tailWord_4317136
  simp only [CollatzResearch.WordTrace]
  refine ⟨78729442843880527486905631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104972590458507369982540841 78729442843880527486905631)
  ·
    refine ⟨118094164265820791230358447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78729442843880527486905631 118094164265820791230358447)
    ·
      refine ⟨177141246398731186845537671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118094164265820791230358447 177141246398731186845537671)
      ·
        refine ⟨265711869598096780268306507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177141246398731186845537671 265711869598096780268306507)
        ·
          refine ⟨398567804397145170402459761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265711869598096780268306507 398567804397145170402459761)
          ·
            refine ⟨298925853297858877801844821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398567804397145170402459761 298925853297858877801844821)
            ·
              refine ⟨3503037343334283724240369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 298925853297858877801844821 3503037343334283724240369)
              ·
                refine ⟨2627278007500712793180277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3503037343334283724240369 2627278007500712793180277)
                ·
                  refine ⟨246307313203191824360651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2627278007500712793180277 246307313203191824360651)
                  ·
                    rfl

theorem cell23_4317136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 8, 2, 5].length) (baseStart_4317136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317136 prefixEnd_4317136 := by exact prefixLift 4317136
  have htrace : WordTrace (prefixWord ++ tailWord_4317136) baseStart_4317136 baseEnd_4317136 := by
    simpa [prefixWord, tailWord_4317136, baseEnd_4317136] using wordTrace_append hprefix tailTrace_4317136
  have hstable : (prefixWord ++ tailWord_4317136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317136).length < 2 ^ (prefixWord ++ tailWord_4317136).sum := by decide
  have hdescent : baseEnd_4317136 < baseStart_4317136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317146 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3]
def baseStart_4317146 : Nat := 118140960795 + 4317146 * 2 ^ 59
def prefixEnd_4317146 : Nat := 4983230072969 + 3 ^ 40 * 4317146 * 2
def baseEnd_4317146 : Nat := 2216770953635271380120813

theorem tailTrace_4317146 : CollatzResearch.WordTrace tailWord_4317146 prefixEnd_4317146 2216770953635271380120813 := by
  unfold tailWord_4317146
  simp only [CollatzResearch.WordTrace]
  refine ⟨39364812604431206670418823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104972833611816551121116861 39364812604431206670418823)
  ·
    refine ⟨59047218906646810005628235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39364812604431206670418823 59047218906646810005628235)
    ·
      refine ⟨88570828359970215008442353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59047218906646810005628235 88570828359970215008442353)
      ·
        refine ⟨66428121269977661256331765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88570828359970215008442353 66428121269977661256331765)
        ·
          refine ⟨6227636369060405742781103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 66428121269977661256331765 6227636369060405742781103)
          ·
            refine ⟨9341454553590608614171655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6227636369060405742781103 9341454553590608614171655)
            ·
              refine ⟨14012181830385912921257483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9341454553590608614171655 14012181830385912921257483)
              ·
                refine ⟨21018272745578869381886225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14012181830385912921257483 21018272745578869381886225)
                ·
                  refine ⟨15763704559184152036414669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21018272745578869381886225 15763704559184152036414669)
                  ·
                    refine ⟨5911389209694057013655501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15763704559184152036414669 5911389209694057013655501)
                    ·
                      refine ⟨2216770953635271380120813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5911389209694057013655501 2216770953635271380120813)
                      ·
                        rfl

theorem cell23_4317146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_4317146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317146 prefixEnd_4317146 := by exact prefixLift 4317146
  have htrace : WordTrace (prefixWord ++ tailWord_4317146) baseStart_4317146 baseEnd_4317146 := by
    simpa [prefixWord, tailWord_4317146, baseEnd_4317146] using wordTrace_append hprefix tailTrace_4317146
  have hstable : (prefixWord ++ tailWord_4317146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317146).length < 2 ^ (prefixWord ++ tailWord_4317146).sum := by decide
  have hdescent : baseEnd_4317146 < baseStart_4317146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317166 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 2, 5]
def baseStart_4317166 : Nat := 118140960795 + 4317166 * 2 ^ 59
def prefixEnd_4317166 : Nat := 4983230072969 + 3 ^ 40 * 4317166 * 2
def baseEnd_4317166 : Nat := 738927074416120433956907

theorem tailTrace_4317166 : CollatzResearch.WordTrace tailWord_4317166 prefixEnd_4317166 738927074416120433956907 := by
  unfold tailWord_4317166
  simp only [CollatzResearch.WordTrace]
  refine ⟨19682497484706546262175419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104973319918434913398268901 19682497484706546262175419)
  ·
    refine ⟨29523746227059819393263129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19682497484706546262175419 29523746227059819393263129)
    ·
      refine ⟨22142809670294864544947347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29523746227059819393263129 22142809670294864544947347)
      ·
        refine ⟨33214214505442296817421021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22142809670294864544947347 33214214505442296817421021)
        ·
          refine ⟨12455330439540861306532883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33214214505442296817421021 12455330439540861306532883)
          ·
            refine ⟨18682995659311291959799325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12455330439540861306532883 18682995659311291959799325)
            ·
              refine ⟨7006123372241734484924747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18682995659311291959799325 7006123372241734484924747)
              ·
                refine ⟨10509185058362601727387121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7006123372241734484924747 10509185058362601727387121)
                ·
                  refine ⟨7881888793771951295540341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10509185058362601727387121 7881888793771951295540341)
                  ·
                    refine ⟨738927074416120433956907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7881888793771951295540341 738927074416120433956907)
                    ·
                      rfl

theorem cell23_4317166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_4317166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317166 prefixEnd_4317166 := by exact prefixLift 4317166
  have htrace : WordTrace (prefixWord ++ tailWord_4317166) baseStart_4317166 baseEnd_4317166 := by
    simpa [prefixWord, tailWord_4317166, baseEnd_4317166] using wordTrace_append hprefix tailTrace_4317166
  have hstable : (prefixWord ++ tailWord_4317166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317166).length < 2 ^ (prefixWord ++ tailWord_4317166).sum := by decide
  have hdescent : baseEnd_4317166 < baseStart_4317166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317196 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 3, 4]
def baseStart_4317196 : Nat := 118140960795 + 4317196 * 2 ^ 59
def prefixEnd_4317196 : Nat := 4983230072969 + 3 ^ 40 * 4317196 * 2
def baseEnd_4317196 : Nat := 738932209222665394831861

theorem tailTrace_4317196 : CollatzResearch.WordTrace tailWord_4317196 prefixEnd_4317196 738932209222665394831861 := by
  unfold tailWord_4317196
  simp only [CollatzResearch.WordTrace]
  refine ⟨78730537033771842610497721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104974049378362456813996961 78730537033771842610497721)
  ·
    refine ⟨59047902775328881957873291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78730537033771842610497721 59047902775328881957873291)
    ·
      refine ⟨88571854162993322936809937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59047902775328881957873291 88571854162993322936809937)
      ·
        refine ⟨66428890622244992202607453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88571854162993322936809937 66428890622244992202607453)
        ·
          refine ⟨24910833983341872075977795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66428890622244992202607453 24910833983341872075977795)
          ·
            refine ⟨37366250975012808113966693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24910833983341872075977795 37366250975012808113966693)
            ·
              refine ⟨7006172057814901521368755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37366250975012808113966693 7006172057814901521368755)
              ·
                refine ⟨10509258086722352282053133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7006172057814901521368755 10509258086722352282053133)
                ·
                  refine ⟨3940971782520882105769925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10509258086722352282053133 3940971782520882105769925)
                  ·
                    refine ⟨738932209222665394831861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3940971782520882105769925 738932209222665394831861)
                    ·
                      rfl

theorem cell23_4317196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_4317196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317196 prefixEnd_4317196 := by exact prefixLift 4317196
  have htrace : WordTrace (prefixWord ++ tailWord_4317196) baseStart_4317196 baseEnd_4317196 := by
    simpa [prefixWord, tailWord_4317196, baseEnd_4317196] using wordTrace_append hprefix tailTrace_4317196
  have hstable : (prefixWord ++ tailWord_4317196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317196).length < 2 ^ (prefixWord ++ tailWord_4317196).sum := by decide
  have hdescent : baseEnd_4317196 < baseStart_4317196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317219 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 3]
def baseStart_4317219 : Nat := 118140960795 + 4317219 * 2 ^ 59
def prefixEnd_4317219 : Nat := 4983230072969 + 3 ^ 40 * 4317219 * 2
def baseEnd_4317219 : Nat := 2216808437723049594507977

theorem tailTrace_4317219 : CollatzResearch.WordTrace tailWord_4317219 prefixEnd_4317219 2216808437723049594507977 := by
  unfold tailWord_4317219
  simp only [CollatzResearch.WordTrace]
  refine ⟨157461912946460360149082711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104974608630973573432721807 157461912946460360149082711)
  ·
    refine ⟨236192869419690540223624067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157461912946460360149082711 236192869419690540223624067)
    ·
      refine ⟨354289304129535810335436101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236192869419690540223624067 354289304129535810335436101)
      ·
        refine ⟨66429244524287964437894269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 354289304129535810335436101 66429244524287964437894269)
        ·
          refine ⟨24910966696607986664210351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66429244524287964437894269 24910966696607986664210351)
          ·
            refine ⟨37366450044911979996315527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24910966696607986664210351 37366450044911979996315527)
            ·
              refine ⟨56049675067367969994473291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37366450044911979996315527 56049675067367969994473291)
              ·
                refine ⟨84074512601051954991709937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56049675067367969994473291 84074512601051954991709937)
                ·
                  refine ⟨63055884450788966243782453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84074512601051954991709937 63055884450788966243782453)
                  ·
                    refine ⟨5911489167261465585354605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 63055884450788966243782453 5911489167261465585354605)
                    ·
                      refine ⟨2216808437723049594507977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5911489167261465585354605 2216808437723049594507977)
                      ·
                        rfl

theorem cell23_4317219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_4317219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317219 prefixEnd_4317219 := by exact prefixLift 4317219
  have htrace : WordTrace (prefixWord ++ tailWord_4317219) baseStart_4317219 baseEnd_4317219 := by
    simpa [prefixWord, tailWord_4317219, baseEnd_4317219] using wordTrace_append hprefix tailTrace_4317219
  have hstable : (prefixWord ++ tailWord_4317219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317219).length < 2 ^ (prefixWord ++ tailWord_4317219).sum := by decide
  have hdescent : baseEnd_4317219 < baseStart_4317219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317230 : List Nat := [4, 1, 3, 1, 1, 2, 3, 3, 1, 4]
def baseStart_4317230 : Nat := 118140960795 + 4317230 * 2 ^ 59
def prefixEnd_4317230 : Nat := 4983230072969 + 3 ^ 40 * 4317230 * 2
def baseEnd_4317230 : Nat := 738938028670083017156809

theorem tailTrace_4317230 : CollatzResearch.WordTrace tailWord_4317230 prefixEnd_4317230 738938028670083017156809 := by
  unfold tailWord_4317230
  simp only [CollatzResearch.WordTrace]
  refine ⟨19682789268677563628466643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 104974876099613672685155429 19682789268677563628466643)
  ·
    refine ⟨29524183903016345442699965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19682789268677563628466643 29524183903016345442699965)
    ·
      refine ⟨11071568963631129541012487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 29524183903016345442699965 11071568963631129541012487)
      ·
        refine ⟨16607353445446694311518731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11071568963631129541012487 16607353445446694311518731)
        ·
          refine ⟨24911030168170041467278097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16607353445446694311518731 24911030168170041467278097)
          ·
            refine ⟨18683272626127531100458573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24911030168170041467278097 18683272626127531100458573)
            ·
              refine ⟨7006227234797824162671965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18683272626127531100458573 7006227234797824162671965)
              ·
                refine ⟨2627335213049184061001987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7006227234797824162671965 2627335213049184061001987)
                ·
                  refine ⟨3941002819573776091502981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2627335213049184061001987 3941002819573776091502981)
                  ·
                    refine ⟨738938028670083017156809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3941002819573776091502981 738938028670083017156809)
                    ·
                      rfl

theorem cell23_4317230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_4317230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317230 prefixEnd_4317230 := by exact prefixLift 4317230
  have htrace : WordTrace (prefixWord ++ tailWord_4317230) baseStart_4317230 baseEnd_4317230 := by
    simpa [prefixWord, tailWord_4317230, baseEnd_4317230] using wordTrace_append hprefix tailTrace_4317230
  have hstable : (prefixWord ++ tailWord_4317230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317230).length < 2 ^ (prefixWord ++ tailWord_4317230).sum := by decide
  have hdescent : baseEnd_4317230 < baseStart_4317230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317259 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 4]
def baseStart_4317259 : Nat := 118140960795 + 4317259 * 2 ^ 59
def prefixEnd_4317259 : Nat := 4983230072969 + 3 ^ 40 * 4317259 * 2
def baseEnd_4317259 : Nat := 2216828976949229438007793

theorem tailTrace_4317259 : CollatzResearch.WordTrace tailWord_4317259 prefixEnd_4317259 2216828976949229438007793 := by
  unfold tailWord_4317259
  simp only [CollatzResearch.WordTrace]
  refine ⟨157463371866315446980538831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104975581244210297987025887 157463371866315446980538831)
  ·
    refine ⟨236195057799473170470808247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157463371866315446980538831 236195057799473170470808247)
    ·
      refine ⟨354292586699209755706212371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236195057799473170470808247 354292586699209755706212371)
      ·
        refine ⟨531438880048814633559318557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354292586699209755706212371 531438880048814633559318557)
        ·
          refine ⟨199289580018305487584744459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 531438880048814633559318557 199289580018305487584744459)
          ·
            refine ⟨298934370027458231377116689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199289580018305487584744459 298934370027458231377116689)
            ·
              refine ⟨224200777520593673532837517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 298934370027458231377116689 224200777520593673532837517)
              ·
                refine ⟨84075291570222627574814069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 224200777520593673532837517 84075291570222627574814069)
                ·
                  refine ⟨7882058584708371335138819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84075291570222627574814069 7882058584708371335138819)
                  ·
                    refine ⟨11823087877062557002708229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7882058584708371335138819 11823087877062557002708229)
                    ·
                      refine ⟨2216828976949229438007793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11823087877062557002708229 2216828976949229438007793)
                      ·
                        rfl

theorem cell23_4317259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 1, 4].length) (baseStart_4317259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317259 prefixEnd_4317259 := by exact prefixLift 4317259
  have htrace : WordTrace (prefixWord ++ tailWord_4317259) baseStart_4317259 baseEnd_4317259 := by
    simpa [prefixWord, tailWord_4317259, baseEnd_4317259] using wordTrace_append hprefix tailTrace_4317259
  have hstable : (prefixWord ++ tailWord_4317259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317259).length < 2 ^ (prefixWord ++ tailWord_4317259).sum := by decide
  have hdescent : baseEnd_4317259 < baseStart_4317259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317290 : List Nat := [3, 1, 3, 2, 3, 1, 3, 1, 1, 5]
def baseStart_4317290 : Nat := 118140960795 + 4317290 * 2 ^ 59
def prefixEnd_4317290 : Nat := 4983230072969 + 3 ^ 40 * 4317290 * 2
def baseEnd_4317290 : Nat := 738948298283172938906717

theorem tailTrace_4317290 : CollatzResearch.WordTrace tailWord_4317290 prefixEnd_4317290 738948298283172938906717 := by
  unfold tailWord_4317290
  simp only [CollatzResearch.WordTrace]
  refine ⟨39366125632300784818729331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104976335019468759516611549 39366125632300784818729331)
  ·
    refine ⟨59049188448451177228093997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39366125632300784818729331 59049188448451177228093997)
    ·
      refine ⟨22143445668169191460535249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59049188448451177228093997 22143445668169191460535249)
      ·
        refine ⟨16607584251126893595401437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22143445668169191460535249 16607584251126893595401437)
        ·
          refine ⟨6227844094172585098275539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16607584251126893595401437 6227844094172585098275539)
          ·
            refine ⟨9341766141258877647413309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6227844094172585098275539 9341766141258877647413309)
            ·
              refine ⟨3503162302972079117779991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9341766141258877647413309 3503162302972079117779991)
              ·
                refine ⟨5254743454458118676669987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3503162302972079117779991 5254743454458118676669987)
                ·
                  refine ⟨7882115181687178015004981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5254743454458118676669987 7882115181687178015004981)
                  ·
                    refine ⟨738948298283172938906717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7882115181687178015004981 738948298283172938906717)
                    ·
                      rfl

theorem cell23_4317290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_4317290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317290 prefixEnd_4317290 := by exact prefixLift 4317290
  have htrace : WordTrace (prefixWord ++ tailWord_4317290) baseStart_4317290 baseEnd_4317290 := by
    simpa [prefixWord, tailWord_4317290, baseEnd_4317290] using wordTrace_append hprefix tailTrace_4317290
  have hstable : (prefixWord ++ tailWord_4317290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317290).length < 2 ^ (prefixWord ++ tailWord_4317290).sum := by decide
  have hdescent : baseEnd_4317290 < baseStart_4317290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317296 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 5]
def baseStart_4317296 : Nat := 118140960795 + 4317296 * 2 ^ 59
def prefixEnd_4317296 : Nat := 4983230072969 + 3 ^ 40 * 4317296 * 2
def baseEnd_4317296 : Nat := 2216847975733445793245123

theorem tailTrace_4317296 : CollatzResearch.WordTrace tailWord_4317296 prefixEnd_4317296 2216847975733445793245123 := by
  unfold tailWord_4317296
  simp only [CollatzResearch.WordTrace]
  refine ⟨78732360683590701149817871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104976480911454268199757161 78732360683590701149817871)
  ·
    refine ⟨118098541025386051724726807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78732360683590701149817871 118098541025386051724726807)
    ·
      refine ⟨177147811538079077587090211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118098541025386051724726807 177147811538079077587090211)
      ·
        refine ⟨265721717307118616380635317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177147811538079077587090211 265721717307118616380635317)
        ·
          refine ⟨24911410997542370285684561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 265721717307118616380635317 24911410997542370285684561)
          ·
            refine ⟨18683558248156777714263421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24911410997542370285684561 18683558248156777714263421)
            ·
              refine ⟨7006334343058791642848783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18683558248156777714263421 7006334343058791642848783)
              ·
                refine ⟨10509501514588187464273175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7006334343058791642848783 10509501514588187464273175)
                ·
                  refine ⟨15764252271882281196409763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10509501514588187464273175 15764252271882281196409763)
                  ·
                    refine ⟨23646378407823421794614645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15764252271882281196409763 23646378407823421794614645)
                    ·
                      refine ⟨2216847975733445793245123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23646378407823421794614645 2216847975733445793245123)
                      ·
                        rfl

theorem cell23_4317296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 5].length) (baseStart_4317296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317296 prefixEnd_4317296 := by exact prefixLift 4317296
  have htrace : WordTrace (prefixWord ++ tailWord_4317296) baseStart_4317296 baseEnd_4317296 := by
    simpa [prefixWord, tailWord_4317296, baseEnd_4317296] using wordTrace_append hprefix tailTrace_4317296
  have hstable : (prefixWord ++ tailWord_4317296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317296).length < 2 ^ (prefixWord ++ tailWord_4317296).sum := by decide
  have hdescent : baseEnd_4317296 < baseStart_4317296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317303 : List Nat := [1, 1, 3, 1, 1, 6, 2, 2, 2, 4]
def baseStart_4317303 : Nat := 118140960795 + 4317303 * 2 ^ 59
def prefixEnd_4317303 : Nat := 4983230072969 + 3 ^ 40 * 4317303 * 2
def baseEnd_4317303 : Nat := 738950523366009088619197

theorem tailTrace_4317303 : CollatzResearch.WordTrace tailWord_4317303 prefixEnd_4317303 738950523366009088619197 := by
  unfold tailWord_4317303
  simp only [CollatzResearch.WordTrace]
  refine ⟨157464976678156042495140563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104976651118770694996760375 157464976678156042495140563)
  ·
    refine ⟨236197465017234063742710845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157464976678156042495140563 236197465017234063742710845)
    ·
      refine ⟨88574049381462773903516567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236197465017234063742710845 88574049381462773903516567)
      ·
        refine ⟨132861074072194160855274851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88574049381462773903516567 132861074072194160855274851)
        ·
          refine ⟨199291611108291241282912277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132861074072194160855274851 199291611108291241282912277)
          ·
            refine ⟨9341794270701151935136513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 199291611108291241282912277 9341794270701151935136513)
            ·
              refine ⟨7006345703025863951352385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9341794270701151935136513 7006345703025863951352385)
              ·
                refine ⟨5254759277269397963514289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7006345703025863951352385 5254759277269397963514289)
                ·
                  refine ⟨3941069457952048472635717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5254759277269397963514289 3941069457952048472635717)
                  ·
                    refine ⟨738950523366009088619197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3941069457952048472635717 738950523366009088619197)
                    ·
                      rfl

theorem cell23_4317303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_4317303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317303 prefixEnd_4317303 := by exact prefixLift 4317303
  have htrace : WordTrace (prefixWord ++ tailWord_4317303) baseStart_4317303 baseEnd_4317303 := by
    simpa [prefixWord, tailWord_4317303, baseEnd_4317303] using wordTrace_append hprefix tailTrace_4317303
  have hstable : (prefixWord ++ tailWord_4317303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317303).length < 2 ^ (prefixWord ++ tailWord_4317303).sum := by decide
  have hdescent : baseEnd_4317303 < baseStart_4317303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317319 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 6]
def baseStart_4317319 : Nat := 118140960795 + 4317319 * 2 ^ 59
def prefixEnd_4317319 : Nat := 4983230072969 + 3 ^ 40 * 4317319 * 2
def baseEnd_4317319 : Nat := 2216859785788499203257517

theorem tailTrace_4317319 : CollatzResearch.WordTrace tailWord_4317319 prefixEnd_4317319 2216859785788499203257517 := by
  unfold tailWord_4317319
  simp only [CollatzResearch.WordTrace]
  refine ⟨157465560246098077227723011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104977040164065384818482007 157465560246098077227723011)
  ·
    refine ⟨236198340369147115841584517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157465560246098077227723011 236198340369147115841584517)
    ·
      refine ⟨44287188819215084220297097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 236198340369147115841584517 44287188819215084220297097)
      ·
        refine ⟨33215391614411313165222823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44287188819215084220297097 33215391614411313165222823)
        ·
          refine ⟨49823087421616969747834235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33215391614411313165222823 49823087421616969747834235)
          ·
            refine ⟨74734631132425454621751353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49823087421616969747834235 74734631132425454621751353)
            ·
              refine ⟨56050973349319090966313515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 74734631132425454621751353 56050973349319090966313515)
              ·
                refine ⟨84076460023978636449470273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56050973349319090966313515 84076460023978636449470273)
                ·
                  refine ⟨63057345017983977337102705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 84076460023978636449470273 63057345017983977337102705)
                  ·
                    refine ⟨47293008763487983002827029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 63057345017983977337102705 47293008763487983002827029)
                    ·
                      refine ⟨2216859785788499203257517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 47293008763487983002827029 2216859785788499203257517)
                      ·
                        rfl

theorem cell23_4317319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_4317319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317319 prefixEnd_4317319 := by exact prefixLift 4317319
  have htrace : WordTrace (prefixWord ++ tailWord_4317319) baseStart_4317319 baseEnd_4317319 := by
    simpa [prefixWord, tailWord_4317319, baseEnd_4317319] using wordTrace_append hprefix tailTrace_4317319
  have hstable : (prefixWord ++ tailWord_4317319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317319).length < 2 ^ (prefixWord ++ tailWord_4317319).sum := by decide
  have hdescent : baseEnd_4317319 < baseStart_4317319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317343 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 3]
def baseStart_4317343 : Nat := 118140960795 + 4317343 * 2 ^ 59
def prefixEnd_4317343 : Nat := 4983230072969 + 3 ^ 40 * 4317343 * 2
def baseEnd_4317343 : Nat := 2216872109324207109357407

theorem tailTrace_4317343 : CollatzResearch.WordTrace tailWord_4317343 prefixEnd_4317343 2216872109324207109357407 := by
  unfold tailWord_4317343
  simp only [CollatzResearch.WordTrace]
  refine ⟨157466435598011129326596683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104977623732007419551064455 157466435598011129326596683)
  ·
    refine ⟨236199653397016693989895025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157466435598011129326596683 236199653397016693989895025)
    ·
      refine ⟨177149740047762520492421269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236199653397016693989895025 177149740047762520492421269)
      ·
        refine ⟨8303894064738868148082247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 177149740047762520492421269 8303894064738868148082247)
        ·
          refine ⟨12455841097108302222123371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8303894064738868148082247 12455841097108302222123371)
          ·
            refine ⟨18683761645662453333185057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12455841097108302222123371 18683761645662453333185057)
            ·
              refine ⟨14012821234246839999888793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18683761645662453333185057 14012821234246839999888793)
              ·
                refine ⟨10509615925685129999916595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14012821234246839999888793 10509615925685129999916595)
                ·
                  refine ⟨15764423888527694999874893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10509615925685129999916595 15764423888527694999874893)
                  ·
                    refine ⟨5911658958197885624953085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15764423888527694999874893 5911658958197885624953085)
                    ·
                      refine ⟨2216872109324207109357407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5911658958197885624953085 2216872109324207109357407)
                      ·
                        rfl

theorem cell23_4317343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_4317343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317343 prefixEnd_4317343 := by exact prefixLift 4317343
  have htrace : WordTrace (prefixWord ++ tailWord_4317343) baseStart_4317343 baseEnd_4317343 := by
    simpa [prefixWord, tailWord_4317343, baseEnd_4317343] using wordTrace_append hprefix tailTrace_4317343
  have hstable : (prefixWord ++ tailWord_4317343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317343).length < 2 ^ (prefixWord ++ tailWord_4317343).sum := by decide
  have hdescent : baseEnd_4317343 < baseStart_4317343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317354 : List Nat := [3, 1, 5, 1, 3, 1, 1, 2, 2, 4]
def baseStart_4317354 : Nat := 118140960795 + 4317354 * 2 ^ 59
def prefixEnd_4317354 : Nat := 4983230072969 + 3 ^ 40 * 4317354 * 2
def baseEnd_4317354 : Nat := 738959252537135522106619

theorem tailTrace_4317354 : CollatzResearch.WordTrace tailWord_4317354 prefixEnd_4317354 738959252537135522106619 := by
  unfold tailWord_4317354
  simp only [CollatzResearch.WordTrace]
  refine ⟨39366709200242819551311779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104977891200647518803498077 39366709200242819551311779)
  ·
    refine ⟨59050063800364229326967669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39366709200242819551311779 59050063800364229326967669)
    ·
      refine ⟨5535943481284146499403219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59050063800364229326967669 5535943481284146499403219)
      ·
        refine ⟨8303915221926219749104829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5535943481284146499403219 8303915221926219749104829)
        ·
          refine ⟨3113968208222332405914311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8303915221926219749104829 3113968208222332405914311)
          ·
            refine ⟨4670952312333498608871467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3113968208222332405914311 4670952312333498608871467)
            ·
              refine ⟨7006428468500247913307201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4670952312333498608871467 7006428468500247913307201)
              ·
                refine ⟨5254821351375185934980401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7006428468500247913307201 5254821351375185934980401)
                ·
                  refine ⟨3941116013531389451235301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5254821351375185934980401 3941116013531389451235301)
                  ·
                    refine ⟨738959252537135522106619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3941116013531389451235301 738959252537135522106619)
                    ·
                      rfl

theorem cell23_4317354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_4317354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317354 prefixEnd_4317354 := by exact prefixLift 4317354
  have htrace : WordTrace (prefixWord ++ tailWord_4317354) baseStart_4317354 baseEnd_4317354 := by
    simpa [prefixWord, tailWord_4317354, baseEnd_4317354] using wordTrace_append hprefix tailTrace_4317354
  have hstable : (prefixWord ++ tailWord_4317354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317354).length < 2 ^ (prefixWord ++ tailWord_4317354).sum := by decide
  have hdescent : baseEnd_4317354 < baseStart_4317354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317376 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 2, 6]
def baseStart_4317376 : Nat := 118140960795 + 4317376 * 2 ^ 59
def prefixEnd_4317376 : Nat := 4983230072969 + 3 ^ 40 * 4317376 * 2
def baseEnd_4317376 : Nat := 738963018061935160081585

theorem tailTrace_4317376 : CollatzResearch.WordTrace tailWord_4317376 prefixEnd_4317376 738963018061935160081585 := by
  unfold tailWord_4317376
  simp only [CollatzResearch.WordTrace]
  refine ⟨78733819603445787981273991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104978426137927717308365321 78733819603445787981273991)
  ·
    refine ⟨118100729405168681971910987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78733819603445787981273991 118100729405168681971910987)
    ·
      refine ⟨177151094107753022957866481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 118100729405168681971910987 177151094107753022957866481)
      ·
        refine ⟨132863320580814767218399861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177151094107753022957866481 132863320580814767218399861)
        ·
          refine ⟨12455936304451384426724987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 132863320580814767218399861 12455936304451384426724987)
          ·
            refine ⟨18683904456677076640087481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12455936304451384426724987 18683904456677076640087481)
            ·
              refine ⟨14012928342507807480065611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18683904456677076640087481 14012928342507807480065611)
              ·
                refine ⟨21019392513761711220098417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14012928342507807480065611 21019392513761711220098417)
                ·
                  refine ⟨15764544385321283415073813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21019392513761711220098417 15764544385321283415073813)
                  ·
                    refine ⟨738963018061935160081585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15764544385321283415073813 738963018061935160081585)
                    ·
                      rfl

theorem cell23_4317376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 2, 6].length) (baseStart_4317376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317376 prefixEnd_4317376 := by exact prefixLift 4317376
  have htrace : WordTrace (prefixWord ++ tailWord_4317376) baseStart_4317376 baseEnd_4317376 := by
    simpa [prefixWord, tailWord_4317376, baseEnd_4317376] using wordTrace_append hprefix tailTrace_4317376
  have hstable : (prefixWord ++ tailWord_4317376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317376).length < 2 ^ (prefixWord ++ tailWord_4317376).sum := by decide
  have hdescent : baseEnd_4317376 < baseStart_4317376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317377 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_4317377 : Nat := 118140960795 + 4317377 * 2 ^ 59
def prefixEnd_4317377 : Nat := 4983230072969 + 3 ^ 40 * 4317377 * 2
def baseEnd_4317377 : Nat := 2216889567666459976332251

theorem tailTrace_4317377 : CollatzResearch.WordTrace tailWord_4317377 prefixEnd_4317377 2216889567666459976332251 := by
  unfold tailWord_4317377
  simp only [CollatzResearch.WordTrace]
  refine ⟨157467675679887953133334385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104978450453258635422222923 157467675679887953133334385)
  ·
    refine ⟨118100756759915964850000789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157467675679887953133334385 118100756759915964850000789)
    ·
      refine ⟨5535972973121060852343787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 118100756759915964850000789 5535972973121060852343787)
      ·
        refine ⟨8303959459681591278515681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5535972973121060852343787 8303959459681591278515681)
        ·
          refine ⟨6227969594761193458886761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8303959459681591278515681 6227969594761193458886761)
          ·
            refine ⟨4670977196070895094165071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6227969594761193458886761 4670977196070895094165071)
            ·
              refine ⟨7006465794106342641247607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4670977196070895094165071 7006465794106342641247607)
              ·
                refine ⟨10509698691159513961871411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7006465794106342641247607 10509698691159513961871411)
                ·
                  refine ⟨15764548036739270942807117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10509698691159513961871411 15764548036739270942807117)
                  ·
                    refine ⟨5911705513777226603552669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15764548036739270942807117 5911705513777226603552669)
                    ·
                      refine ⟨2216889567666459976332251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5911705513777226603552669 2216889567666459976332251)
                      ·
                        rfl

theorem cell23_4317377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_4317377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317377 prefixEnd_4317377 := by exact prefixLift 4317377
  have htrace : WordTrace (prefixWord ++ tailWord_4317377) baseStart_4317377 baseEnd_4317377 := by
    simpa [prefixWord, tailWord_4317377, baseEnd_4317377] using wordTrace_append hprefix tailTrace_4317377
  have hstable : (prefixWord ++ tailWord_4317377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317377).length < 2 ^ (prefixWord ++ tailWord_4317377).sum := by decide
  have hdescent : baseEnd_4317377 < baseStart_4317377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317386 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 2, 1, 5]
def baseStart_4317386 : Nat := 118140960795 + 4317386 * 2 ^ 59
def prefixEnd_4317386 : Nat := 4983230072969 + 3 ^ 40 * 4317386 * 2
def baseEnd_4317386 : Nat := 2216894188992350441119709

theorem tailTrace_4317386 : CollatzResearch.WordTrace tailWord_4317386 prefixEnd_4317386 2216894188992350441119709 := by
  unfold tailWord_4317386
  simp only [CollatzResearch.WordTrace]
  refine ⟨39367000984213836917603003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104978669291236898446941341 39367000984213836917603003)
  ·
    refine ⟨59050501476320755376404505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39367000984213836917603003 59050501476320755376404505)
    ·
      refine ⟨44287876107240566532303379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59050501476320755376404505 44287876107240566532303379)
      ·
        refine ⟨66431814160860849798455069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44287876107240566532303379 66431814160860849798455069)
        ·
          refine ⟨24911930310322818674420651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 66431814160860849798455069 24911930310322818674420651)
          ·
            refine ⟨37367895465484228011630977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24911930310322818674420651 37367895465484228011630977)
            ·
              refine ⟨28025921599113171008723233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37367895465484228011630977 28025921599113171008723233)
              ·
                refine ⟨21019441199334878256542425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28025921599113171008723233 21019441199334878256542425)
                ·
                  refine ⟨15764580899501158692406819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21019441199334878256542425 15764580899501158692406819)
                  ·
                    refine ⟨23646871349251738038610229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15764580899501158692406819 23646871349251738038610229)
                    ·
                      refine ⟨2216894188992350441119709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 23646871349251738038610229 2216894188992350441119709)
                      ·
                        rfl

theorem cell23_4317386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_4317386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317386 prefixEnd_4317386 := by exact prefixLift 4317386
  have htrace : WordTrace (prefixWord ++ tailWord_4317386) baseStart_4317386 baseEnd_4317386 := by
    simpa [prefixWord, tailWord_4317386, baseEnd_4317386] using wordTrace_append hprefix tailTrace_4317386
  have hstable : (prefixWord ++ tailWord_4317386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317386).length < 2 ^ (prefixWord ++ tailWord_4317386).sum := by decide
  have hdescent : baseEnd_4317386 < baseStart_4317386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317400 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 4, 2, 2]
def baseStart_4317400 : Nat := 118140960795 + 4317400 * 2 ^ 59
def prefixEnd_4317400 : Nat := 4983230072969 + 3 ^ 40 * 4317400 * 2
def baseEnd_4317400 : Nat := 2216901377721513386344645

theorem tailTrace_4317400 : CollatzResearch.WordTrace tailWord_4317400 prefixEnd_4317400 2216901377721513386344645 := by
  unfold tailWord_4317400
  simp only [CollatzResearch.WordTrace]
  refine ⟨78734257279402314030710827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104979009705869752040947769 78734257279402314030710827)
  ·
    refine ⟨118101385919103471046066241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 78734257279402314030710827 118101385919103471046066241)
    ·
      refine ⟨88576039439327603284549681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 118101385919103471046066241 88576039439327603284549681)
      ·
        refine ⟨66432029579495702463412261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88576039439327603284549681 66432029579495702463412261)
        ·
          refine ⟨12456005546155444211889799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 66432029579495702463412261 12456005546155444211889799)
          ·
            refine ⟨18684008319233166317834699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12456005546155444211889799 18684008319233166317834699)
            ·
              refine ⟨28026012478849749476752049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18684008319233166317834699 28026012478849749476752049)
              ·
                refine ⟨21019509359137312107564037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28026012478849749476752049 21019509359137312107564037)
                ·
                  refine ⟨3941158004838246020168257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21019509359137312107564037 3941158004838246020168257)
                  ·
                    refine ⟨2955868503628684515126193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3941158004838246020168257 2955868503628684515126193)
                    ·
                      refine ⟨2216901377721513386344645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2955868503628684515126193 2216901377721513386344645)
                      ·
                        rfl

theorem cell23_4317400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_4317400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317400 prefixEnd_4317400 := by exact prefixLift 4317400
  have htrace : WordTrace (prefixWord ++ tailWord_4317400) baseStart_4317400 baseEnd_4317400 := by
    simpa [prefixWord, tailWord_4317400, baseEnd_4317400] using wordTrace_append hprefix tailTrace_4317400
  have hstable : (prefixWord ++ tailWord_4317400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317400).length < 2 ^ (prefixWord ++ tailWord_4317400).sum := by decide
  have hdescent : baseEnd_4317400 < baseStart_4317400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317423 : List Nat := [1, 1, 2, 1, 6, 3, 1, 1, 7]
def baseStart_4317423 : Nat := 118140960795 + 4317423 * 2 ^ 59
def prefixEnd_4317423 : Nat := 4983230072969 + 3 ^ 40 * 4317423 * 2
def baseEnd_4317423 : Nat := 246323687530729644039671

theorem tailTrace_4317423 : CollatzResearch.WordTrace tailWord_4317423 prefixEnd_4317423 246323687530729644039671 := by
  unfold tailWord_4317423
  simp only [CollatzResearch.WordTrace]
  refine ⟨157469353437721302989508923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104979568958480868659672615 157469353437721302989508923)
  ·
    refine ⟨236204030156581954484263385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157469353437721302989508923 236204030156581954484263385)
    ·
      refine ⟨177153022617436465863197539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 236204030156581954484263385 177153022617436465863197539)
      ·
        refine ⟨265729533926154698794796309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 177153022617436465863197539 265729533926154698794796309)
        ·
          refine ⟨12456071902788501506006077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 265729533926154698794796309 12456071902788501506006077)
          ·
            refine ⟨4671026963545688064752279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12456071902788501506006077 4671026963545688064752279)
            ·
              refine ⟨7006540445318532097128419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4671026963545688064752279 7006540445318532097128419)
              ·
                refine ⟨10509810667977798145692629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7006540445318532097128419 10509810667977798145692629)
                ·
                  refine ⟨246323687530729644039671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10509810667977798145692629 246323687530729644039671)
                  ·
                    rfl

theorem cell23_4317423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 7].length) (baseStart_4317423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317423 prefixEnd_4317423 := by exact prefixLift 4317423
  have htrace : WordTrace (prefixWord ++ tailWord_4317423) baseStart_4317423 baseEnd_4317423 := by
    simpa [prefixWord, tailWord_4317423, baseEnd_4317423] using wordTrace_append hprefix tailTrace_4317423
  have hstable : (prefixWord ++ tailWord_4317423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317423).length < 2 ^ (prefixWord ++ tailWord_4317423).sum := by decide
  have hdescent : baseEnd_4317423 < baseStart_4317423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317434 : List Nat := [3, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2]
def baseStart_4317434 : Nat := 118140960795 + 4317434 * 2 ^ 59
def prefixEnd_4317434 : Nat := 4983230072969 + 3 ^ 40 * 4317434 * 2
def baseEnd_4317434 : Nat := 2216918836063766253319489

theorem tailTrace_4317434 : CollatzResearch.WordTrace tailWord_4317434 prefixEnd_4317434 2216918836063766253319489 := by
  unfold tailWord_4317434
  simp only [CollatzResearch.WordTrace]
  refine ⟨39367438660170362967039839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 104979836427120967912106237 39367438660170362967039839)
  ·
    refine ⟨59051157990255544450559759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39367438660170362967039839 59051157990255544450559759)
    ·
      refine ⟨88576736985383316675839639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59051157990255544450559759 88576736985383316675839639)
      ·
        refine ⟨132865105478074975013759459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88576736985383316675839639 132865105478074975013759459)
        ·
          refine ⟨199297658217112462520639189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132865105478074975013759459 199297658217112462520639189)
          ·
            refine ⟨4671038864463573340327481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 199297658217112462520639189 4671038864463573340327481)
            ·
              refine ⟨3503279148347680005245611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4671038864463573340327481 3503279148347680005245611)
              ·
                refine ⟨5254918722521520007868417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3503279148347680005245611 5254918722521520007868417)
                ·
                  refine ⟨3941189041891140005901313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5254918722521520007868417 3941189041891140005901313)
                  ·
                    refine ⟨2955891781418355004425985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3941189041891140005901313 2955891781418355004425985)
                    ·
                      refine ⟨2216918836063766253319489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2955891781418355004425985 2216918836063766253319489)
                      ·
                        rfl

theorem cell23_4317434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2].length) (baseStart_4317434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317434 prefixEnd_4317434 := by exact prefixLift 4317434
  have htrace : WordTrace (prefixWord ++ tailWord_4317434) baseStart_4317434 baseEnd_4317434 := by
    simpa [prefixWord, tailWord_4317434, baseEnd_4317434] using wordTrace_append hprefix tailTrace_4317434
  have hstable : (prefixWord ++ tailWord_4317434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317434).length < 2 ^ (prefixWord ++ tailWord_4317434).sum := by decide
  have hdescent : baseEnd_4317434 < baseStart_4317434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317473 : List Nat := [1, 2, 3, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_4317473 : Nat := 118140960795 + 4317473 * 2 ^ 59
def prefixEnd_4317473 : Nat := 4983230072969 + 3 ^ 40 * 4317473 * 2
def baseEnd_4317473 : Nat := 2216938861809291600731809

theorem tailTrace_4317473 : CollatzResearch.WordTrace tailWord_4317473 prefixEnd_4317473 2216938861809291600731809 := by
  unfold tailWord_4317473
  simp only [CollatzResearch.WordTrace]
  refine ⟨157471177087540161528829073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104980784725026774352552715 157471177087540161528829073)
  ·
    refine ⟨118103382815655121146621805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 157471177087540161528829073 118103382815655121146621805)
    ·
      refine ⟨44288768555870670429983177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 118103382815655121146621805 44288768555870670429983177)
      ·
        refine ⟨33216576416903002822487383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44288768555870670429983177 33216576416903002822487383)
        ·
          refine ⟨49824864625354504233731075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33216576416903002822487383 49824864625354504233731075)
          ·
            refine ⟨74737296938031756350596613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 49824864625354504233731075 74737296938031756350596613)
            ·
              refine ⟨14013243175880954315736865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 74737296938031756350596613 14013243175880954315736865)
              ·
                refine ⟨10509932381910715736802649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14013243175880954315736865 10509932381910715736802649)
                ·
                  refine ⟨7882449286433036802601987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10509932381910715736802649 7882449286433036802601987)
                  ·
                    refine ⟨11823673929649555203902981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7882449286433036802601987 11823673929649555203902981)
                    ·
                      refine ⟨2216938861809291600731809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11823673929649555203902981 2216938861809291600731809)
                      ·
                        rfl

theorem cell23_4317473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_4317473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317473 prefixEnd_4317473 := by exact prefixLift 4317473
  have htrace : WordTrace (prefixWord ++ tailWord_4317473) baseStart_4317473 baseEnd_4317473 := by
    simpa [prefixWord, tailWord_4317473, baseEnd_4317473] using wordTrace_append hprefix tailTrace_4317473
  have hstable : (prefixWord ++ tailWord_4317473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317473).length < 2 ^ (prefixWord ++ tailWord_4317473).sum := by decide
  have hdescent : baseEnd_4317473 < baseStart_4317473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317493 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 1, 4, 3]
def baseStart_4317493 : Nat := 118140960795 + 4317493 * 2 ^ 59
def prefixEnd_4317493 : Nat := 4983230072969 + 3 ^ 40 * 4317493 * 2
def baseEnd_4317493 : Nat := 2216949131422381522481717

theorem tailTrace_4317493 : CollatzResearch.WordTrace tailWord_4317493 prefixEnd_4317493 2216949131422381522481717 := by
  unfold tailWord_4317493
  simp only [CollatzResearch.WordTrace]
  refine ⟨157471906547467704944557133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104981271031645136629704755 157471906547467704944557133)
  ·
    refine ⟨59051964955300389354208925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157471906547467704944557133 59051964955300389354208925)
    ·
      refine ⟨22144486858237646007828347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59051964955300389354208925 22144486858237646007828347)
      ·
        refine ⟨33216730287356469011742521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22144486858237646007828347 33216730287356469011742521)
        ·
          refine ⟨24912547715517351758806891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33216730287356469011742521 24912547715517351758806891)
          ·
            refine ⟨37368821573276027638210337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24912547715517351758806891 37368821573276027638210337)
            ·
              refine ⟨28026616179957020728657753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37368821573276027638210337 28026616179957020728657753)
              ·
                refine ⟨21019962134967765546493315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28026616179957020728657753 21019962134967765546493315)
                ·
                  refine ⟨31529943202451648319739973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21019962134967765546493315 31529943202451648319739973)
                  ·
                    refine ⟨5911864350459684059951245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 31529943202451648319739973 5911864350459684059951245)
                    ·
                      refine ⟨2216949131422381522481717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5911864350459684059951245 2216949131422381522481717)
                      ·
                        rfl

theorem cell23_4317493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_4317493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317493 prefixEnd_4317493 := by exact prefixLift 4317493
  have htrace : WordTrace (prefixWord ++ tailWord_4317493) baseStart_4317493 baseEnd_4317493 := by
    simpa [prefixWord, tailWord_4317493, baseEnd_4317493] using wordTrace_append hprefix tailTrace_4317493
  have hstable : (prefixWord ++ tailWord_4317493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317493).length < 2 ^ (prefixWord ++ tailWord_4317493).sum := by decide
  have hdescent : baseEnd_4317493 < baseStart_4317493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317557 : List Nat := [1, 3, 4, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_4317557 : Nat := 118140960795 + 4317557 * 2 ^ 59
def prefixEnd_4317557 : Nat := 4983230072969 + 3 ^ 40 * 4317557 * 2
def baseEnd_4317557 : Nat := 2216981994184269272081423

theorem tailTrace_4317557 : CollatzResearch.WordTrace tailWord_4317557 prefixEnd_4317557 2216981994184269272081423 := by
  unfold tailWord_4317557
  simp only [CollatzResearch.WordTrace]
  refine ⟨157474240819235843874886925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104982827212823895916591283 157474240819235843874886925)
  ·
    refine ⟨59052840307213441453082597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 157474240819235843874886925 59052840307213441453082597)
    ·
      refine ⟨11072407557602520272452987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59052840307213441453082597 11072407557602520272452987)
      ·
        refine ⟨16608611336403780408679481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11072407557602520272452987 16608611336403780408679481)
        ·
          refine ⟨12456458502302835306509611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16608611336403780408679481 12456458502302835306509611)
          ·
            refine ⟨18684687753454252959764417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12456458502302835306509611 18684687753454252959764417)
            ·
              refine ⟨14013515815090689719823313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18684687753454252959764417 14013515815090689719823313)
              ·
                refine ⟨10510136861318017289867485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14013515815090689719823313 10510136861318017289867485)
                ·
                  refine ⟨3941301322994256483700307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10510136861318017289867485 3941301322994256483700307)
                  ·
                    refine ⟨5911951984491384725550461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3941301322994256483700307 5911951984491384725550461)
                    ·
                      refine ⟨2216981994184269272081423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5911951984491384725550461 2216981994184269272081423)
                      ·
                        rfl

theorem cell23_4317557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_4317557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317557 prefixEnd_4317557 := by exact prefixLift 4317557
  have htrace : WordTrace (prefixWord ++ tailWord_4317557) baseStart_4317557 baseEnd_4317557 := by
    simpa [prefixWord, tailWord_4317557, baseEnd_4317557] using wordTrace_append hprefix tailTrace_4317557
  have hstable : (prefixWord ++ tailWord_4317557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317557).length < 2 ^ (prefixWord ++ tailWord_4317557).sum := by decide
  have hdescent : baseEnd_4317557 < baseStart_4317557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317580 : List Nat := [2, 2, 1, 2, 1, 4, 2, 3, 1, 1, 4]
def baseStart_4317580 : Nat := 118140960795 + 4317580 * 2 ^ 59
def prefixEnd_4317580 : Nat := 4983230072969 + 3 ^ 40 * 4317580 * 2
def baseEnd_4317580 : Nat := 2216993804239322682093817

theorem tailTrace_4317580 : CollatzResearch.WordTrace tailWord_4317580 prefixEnd_4317580 2216993804239322682093817 := by
  unfold tailWord_4317580
  simp only [CollatzResearch.WordTrace]
  refine ⟨78737539849076259401487097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 104983386465435012535316129 78737539849076259401487097)
  ·
    refine ⟨59053154886807194551115323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 78737539849076259401487097 59053154886807194551115323)
    ·
      refine ⟨88579732330210791826672985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59053154886807194551115323 88579732330210791826672985)
      ·
        refine ⟨66434799247658093870004739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 88579732330210791826672985 66434799247658093870004739)
        ·
          refine ⟨99652198871487140805007109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66434799247658093870004739 99652198871487140805007109)
          ·
            refine ⟨18684787288403838900938833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 99652198871487140805007109 18684787288403838900938833)
            ·
              refine ⟨14013590466302879175704125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18684787288403838900938833 14013590466302879175704125)
              ·
                refine ⟨5255096424863579690889047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14013590466302879175704125 5255096424863579690889047)
                ·
                  refine ⟨7882644637295369536333571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5255096424863579690889047 7882644637295369536333571)
                  ·
                    refine ⟨11823966955943054304500357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7882644637295369536333571 11823966955943054304500357)
                    ·
                      refine ⟨2216993804239322682093817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11823966955943054304500357 2216993804239322682093817)
                      ·
                        rfl

theorem cell23_4317580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_4317580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317580 prefixEnd_4317580 := by exact prefixLift 4317580
  have htrace : WordTrace (prefixWord ++ tailWord_4317580) baseStart_4317580 baseEnd_4317580 := by
    simpa [prefixWord, tailWord_4317580, baseEnd_4317580] using wordTrace_append hprefix tailTrace_4317580
  have hstable : (prefixWord ++ tailWord_4317580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317580).length < 2 ^ (prefixWord ++ tailWord_4317580).sum := by decide
  have hdescent : baseEnd_4317580 < baseStart_4317580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317603 : List Nat := [1, 1, 1, 4, 1, 5, 2, 8]
def baseStart_4317603 : Nat := 118140960795 + 4317603 * 2 ^ 59
def prefixEnd_4317603 : Nat := 4983230072969 + 3 ^ 40 * 4317603 * 2
def baseEnd_4317603 : Nat := 82111319047939855263193

theorem tailTrace_4317603 : CollatzResearch.WordTrace tailWord_4317603 prefixEnd_4317603 82111319047939855263193 := by
  unfold tailWord_4317603
  simp only [CollatzResearch.WordTrace]
  refine ⟨157475918577069193731061463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104983945718046129154040975 157475918577069193731061463)
  ·
    refine ⟨236213877865603790596592195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157475918577069193731061463 236213877865603790596592195)
    ·
      refine ⟨354320816798405685894888293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236213877865603790596592195 354320816798405685894888293)
      ·
        refine ⟨66435153149701066105291555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 354320816798405685894888293 66435153149701066105291555)
        ·
          refine ⟨99652729724551599157937333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 66435153149701066105291555 99652729724551599157937333)
          ·
            refine ⟨9342443411676712421056625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 99652729724551599157937333 9342443411676712421056625)
            ·
              refine ⟨7006832558757534315792469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9342443411676712421056625 7006832558757534315792469)
              ·
                refine ⟨82111319047939855263193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7006832558757534315792469 82111319047939855263193)
                ·
                  rfl

theorem cell23_4317603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 8].length) (baseStart_4317603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317603 prefixEnd_4317603 := by exact prefixLift 4317603
  have htrace : WordTrace (prefixWord ++ tailWord_4317603) baseStart_4317603 baseEnd_4317603 := by
    simpa [prefixWord, tailWord_4317603, baseEnd_4317603] using wordTrace_append hprefix tailTrace_4317603
  have hstable : (prefixWord ++ tailWord_4317603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317603).length < 2 ^ (prefixWord ++ tailWord_4317603).sum := by decide
  have hdescent : baseEnd_4317603 < baseStart_4317603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4317607 : List Nat := [1, 1, 6, 1, 1, 3, 1, 3, 2, 4]
def baseStart_4317607 : Nat := 118140960795 + 4317607 * 2 ^ 59
def prefixEnd_4317607 : Nat := 4983230072969 + 3 ^ 40 * 4317607 * 2
def baseEnd_4317607 : Nat := 739002556072331358818731

theorem tailTrace_4317607 : CollatzResearch.WordTrace tailWord_4317607 prefixEnd_4317607 739002556072331358818731 := by
  unfold tailWord_4317607
  simp only [CollatzResearch.WordTrace]
  refine ⟨157476064469054702414207075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 104984042979369801609471383 157476064469054702414207075)
  ·
    refine ⟨236214096703582053621310613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157476064469054702414207075 236214096703582053621310613)
    ·
      refine ⟨11072535782980408763498935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 236214096703582053621310613 11072535782980408763498935)
      ·
        refine ⟨16608803674470613145248403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11072535782980408763498935 16608803674470613145248403)
        ·
          refine ⟨24913205511705919717872605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16608803674470613145248403 24913205511705919717872605)
          ·
            refine ⟨9342452066889719894202227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24913205511705919717872605 9342452066889719894202227)
            ·
              refine ⟨14013678100334579841303341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9342452066889719894202227 14013678100334579841303341)
              ·
                refine ⟨5255129287625467440488753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14013678100334579841303341 5255129287625467440488753)
                ·
                  refine ⟨3941346965719100580366565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5255129287625467440488753 3941346965719100580366565)
                  ·
                    refine ⟨739002556072331358818731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3941346965719100580366565 739002556072331358818731)
                    ·
                      rfl

theorem cell23_4317607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_4317607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4317607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4317607 prefixEnd_4317607 := by exact prefixLift 4317607
  have htrace : WordTrace (prefixWord ++ tailWord_4317607) baseStart_4317607 baseEnd_4317607 := by
    simpa [prefixWord, tailWord_4317607, baseEnd_4317607] using wordTrace_append hprefix tailTrace_4317607
  have hstable : (prefixWord ++ tailWord_4317607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4317607).length < 2 ^ (prefixWord ++ tailWord_4317607).sum := by decide
  have hdescent : baseEnd_4317607 < baseStart_4317607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4317607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
